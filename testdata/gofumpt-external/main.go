package main

import (
	"io"
	"os"

	"github.com/ercJuL/gofumpt/format"
)

func main() {
	orig, err := io.ReadAll(os.Stdin)
	if err != nil {
		panic(err)
	}
	formatted, err := format.Source(orig, format.Options{
		LangVersion: "v1.16",
	})
	if err != nil {
		panic(err)
	}
	os.Stdout.Write(formatted)
}
