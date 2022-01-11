// fork go/ast/import.go

package format

import (
	"fmt"
	"go/ast"
	"go/token"
	"reflect"
	"sort"
	"strconv"
	"strings"
)

// SortImports sorts runs of consecutive import lines in import blocks in f.
// It also removes duplicate imports when it is possible to do so without data loss.
func SortImports(localPrefix string, fset *token.FileSet, f *ast.File) {
	for _, d := range f.Decls {
		d, ok := d.(*ast.GenDecl)
		if !ok || d.Tok != token.IMPORT {
			// Not an import declaration, so we're done.
			// Imports are always first.
			break
		}

		if !d.Lparen.IsValid() {
			// Not a block: sorted by default.
			continue
		}

		// Identify and sort runs of specs on successive lines.
		//i := 0
		//specs := d.Specs[:0]
		//for j, s := range d.Specs {
		//	if j > i && lineAt(fset, s.Pos()) > 1+lineAt(fset, d.Specs[j-1].End()) {
		//		// j begins a new run. End this one.
		//		specs = append(specs, sortSpecs(localPrefix, fset, f, d.Specs[i:j])...)
		//		i = j
		//	}
		//}
		specs := sortSpecs(localPrefix, fset, f, d.Specs)
		d.Specs = specs

		// Deduping can leave a blank line before the rparen; clean that up.
		if len(d.Specs) > 0 {
			lastSpec := d.Specs[len(d.Specs)-1]
			lastLine := lineAt(fset, lastSpec.Pos())
			rParenLine := lineAt(fset, d.Rparen)
			for rParenLine > lastLine+1 {
				rParenLine--
				fset.File(d.Rparen).MergeLine(rParenLine)
			}
		}
		nowGroup := 0

		for _, spec := range d.Specs {
			ipath := importPath(spec)
			iname := importName(spec)
			igroup := importGroup(localPrefix, ipath, iname)
			if nowGroup < igroup {
				spec := spec.(*ast.ImportSpec)
				addNewline(fset, spec.Pos()-1)
				addNewline(fset, spec.Pos())
				nowGroup = igroup
			}
		}
	}
}

func lineAt(fset *token.FileSet, pos token.Pos) int {
	return fset.PositionFor(pos, false).Line
}

func importPath(s ast.Spec) string {
	t, err := strconv.Unquote(s.(*ast.ImportSpec).Path.Value)
	if err == nil {
		return t
	}
	return ""
}

func importName(s ast.Spec) string {
	n := s.(*ast.ImportSpec).Name
	if n == nil {
		return ""
	}
	return n.Name
}

func importComment(s ast.Spec) string {
	c := s.(*ast.ImportSpec).Comment
	if c == nil {
		return ""
	}
	return c.Text()
}

// collapse indicates whether prev may be removed, leaving only next.
func collapse(prev, next ast.Spec) bool {
	if importPath(next) != importPath(prev) || importName(next) != importName(prev) {
		return false
	}
	return prev.(*ast.ImportSpec).Comment == nil
}

type posSpan struct {
	Start token.Pos
	End   token.Pos
}

type cgPos struct {
	left bool // true if comment is to the left of the spec, false otherwise.
	cg   *ast.CommentGroup
}

func sortSpecs(localPrefix string, fset *token.FileSet, f *ast.File, specs []ast.Spec) []ast.Spec {
	// Can't short-circuit here even if specs are already sorted,
	// since they might yet need deduplication.
	// A lone import, however, may be safely ignored.
	if len(specs) <= 1 {
		return specs
	}

	// Record positions for specs.
	pos := make([]posSpan, len(specs))
	for i, s := range specs {
		pos[i] = posSpan{s.Pos(), s.End()}
	}

	// Identify comments in this range.
	begSpecs := pos[0].Start
	endSpecs := pos[len(pos)-1].End
	beg := fset.File(begSpecs).LineStart(lineAt(fset, begSpecs))
	endLine := lineAt(fset, endSpecs)
	endFile := fset.File(endSpecs)
	var end token.Pos
	if endLine == endFile.LineCount() {
		end = endSpecs
	} else {
		end = endFile.LineStart(endLine + 1) // beginning of next line
	}
	first := len(f.Comments)
	last := -1
	for i, g := range f.Comments {
		if g.End() >= end {
			break
		}
		// g.End() < end
		if beg <= g.Pos() {
			// comment is within the range [beg, end[ of import declarations
			if i < first {
				first = i
			}
			if i > last {
				last = i
			}
		}
	}

	var comments []*ast.CommentGroup
	if last >= 0 {
		comments = f.Comments[first : last+1]
	}

	// Assign each comment to the import spec on the same line.
	importComments := map[*ast.ImportSpec][]cgPos{}
	specIndex := 0
	for _, g := range comments {
		for specIndex+1 < len(specs) && pos[specIndex+1].Start <= g.Pos() {
			specIndex++
		}
		var left bool
		// A block comment can appear before the first import spec.
		if specIndex == 0 && pos[specIndex].Start > g.Pos() {
			left = true
		} else if specIndex+1 < len(specs) && // Or it can appear on the left of an import spec.
			lineAt(fset, pos[specIndex].Start)+1 == lineAt(fset, g.Pos()) {
			specIndex++
			left = true
		}
		s := specs[specIndex].(*ast.ImportSpec)
		importComments[s] = append(importComments[s], cgPos{left: left, cg: g})
	}

	// Sort the import specs by import path.
	// Remove duplicates, when possible without data loss.
	// Reassign the import paths to have the same position sequence.
	// Reassign each comment to the spec on the same line.
	// Sort the comments by new position.
	sort.Sort(byImportSpec{localPrefix, specs})

	// Dedup. Thanks to our sorting, we can just consider
	// adjacent pairs of imports.
	deduped := specs[:0]
	for i, s := range specs {
		if i == len(specs)-1 || !collapse(s, specs[i+1]) {
			deduped = append(deduped, s)
		} else {
			p := s.Pos()
			fset.File(p).MergeLine(lineAt(fset, p))
		}
	}
	specs = deduped

	// Fix up comment positions
	for i, s := range specs {
		s := s.(*ast.ImportSpec)
		if s.Name != nil {
			s.Name.NamePos = pos[i].Start
		}
		s.Path.ValuePos = pos[i].Start
		s.EndPos = pos[i].End
		for _, g := range importComments[s] {
			for _, c := range g.cg.List {
				if g.left {
					c.Slash = pos[i].Start - 1
				} else {
					// An import spec can have both block comment and a line comment
					// to its right. In that case, both of them will have the same pos.
					// But while formatting the AST, the line comment gets moved to
					// after the block comment.
					c.Slash = pos[i].End
				}
			}
		}
	}

	sort.Sort(byCommentPos(comments))

	// Fixup comments can insert blank lines, because import specs are on different lines.
	// We remove those blank lines here by merging import spec to the first import spec line.
	firstSpecLine := fset.Position(specs[0].Pos()).Line
	for _, s := range specs[1:] {
		p := s.Pos()
		line := fset.File(p).Line(p)
		for previousLine := line - 1; previousLine >= firstSpecLine; {
			fset.File(p).MergeLine(previousLine)
			previousLine--
		}
	}
	for s, _ := range importComments {
		addNewline(fset, s.Pos()-1)
		addNewline(fset, s.Pos())
	}

	return specs
}

// ================ hack code

func addNewline(fset *token.FileSet, at token.Pos) {
	f := fset.File(at)
	offset := f.Offset(at)

	field := reflect.ValueOf(f).Elem().FieldByName("lines")
	n := field.Len()
	lines := make([]int, 0, n+1)
	for i := 0; i < n; i++ {
		cur := int(field.Index(i).Int())
		if offset == cur {
			// This newline already exists; do nothing. Duplicate
			// newlines can't exist.
			return
		}
		if offset >= 0 && offset < cur {
			lines = append(lines, offset)
			offset = -1
		}
		lines = append(lines, cur)
	}
	if offset >= 0 {
		lines = append(lines, offset)
	}
	if !f.SetLines(lines) {
		panic(fmt.Sprintf("could not set lines to %v", lines))
	}
}

// 6 含 import_name 本地包
// 5 本地包
// 4 appengine
// 3 含 import_name包含 .
// 2 包含 .
// 1 含 import_name 系统内置包
// 0 系统内置包
var importToGroup = []func(localPrefix, importPath, importName string) (num int, ok bool){
	func(localPrefix, importPath, importName string) (num int, ok bool) {
		if localPrefix == "" {
			return
		}
		for _, p := range strings.Split(localPrefix, ",") {
			if strings.HasPrefix(importPath, p) || strings.TrimSuffix(p, "/") == importPath {
				if len(importName) > 0 {
					return 6, true
				}
				return 5, true
			}
		}
		return
	},
	func(_, importPath, importName string) (num int, ok bool) {
		if strings.HasPrefix(importPath, "appengine") {
			return 4, true
		}
		return
	},
	func(_, importPath, importName string) (num int, ok bool) {
		firstComponent := strings.Split(importPath, "/")[0]
		if strings.Contains(firstComponent, ".") {
			if len(importName) > 0 {
				return 3, true
			}
			return 2, true
		}
		return
	},
	func(_, _, importName string) (num int, ok bool) {
		if len(importName) > 0 {
			return 1, true
		}
		return 0, true
	},
}

func importGroup(localPrefix, importPath, importName string) int {
	for _, fn := range importToGroup {
		if n, ok := fn(localPrefix, importPath, importName); ok {
			return n
		}
	}
	return 0
}

type byImportSpec struct {
	localPrefix string
	specs       []ast.Spec // slice of *ast.ImportSpec
}

func (x byImportSpec) Len() int      { return len(x.specs) }
func (x byImportSpec) Swap(i, j int) { x.specs[i], x.specs[j] = x.specs[j], x.specs[i] }
func (x byImportSpec) Less(i, j int) bool {
	ipath := importPath(x.specs[i])
	jpath := importPath(x.specs[j])

	iname := importName(x.specs[i])
	jname := importName(x.specs[j])

	igroup := importGroup(x.localPrefix, ipath, iname)
	jgroup := importGroup(x.localPrefix, jpath, jname)

	if igroup != jgroup {
		return igroup < jgroup
	}
	if ipath != jpath {
		return ipath < jpath
	}
	if iname != jname {
		return iname < jname
	}
	return importComment(x.specs[i]) < importComment(x.specs[j])
}

type byCommentPos []*ast.CommentGroup

func (x byCommentPos) Len() int           { return len(x) }
func (x byCommentPos) Swap(i, j int)      { x[i], x[j] = x[j], x[i] }
func (x byCommentPos) Less(i, j int) bool { return x[i].Pos() < x[j].Pos() }
