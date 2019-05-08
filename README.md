# Introduction

This is an [Isabelle/HOL](https://isabelle.in.tum.de) theory that describes and proves the correctness of the Cap9 kernel specification. There is [a pdf version](Cap9IsabelleSpec.pdf) of this theory, but you are free to install Isabelle and open it directly.

Warning: this is work in progress, so everything is subject to change.

# Build

To manually build a pdf or html versions of the theory you need to install the following prerequisites:

* Isabelle2018
* pdflatex
* make

Make sure that `isabelle` command is available from the terminal: you may need to manually add the path to the Isabelle bin directory to the PATH environment variable.

## PDF

To build a pdf file just run the following command:

```console
$ make pdf
```

The file will be created in the `output` folder.

## HTML

It is also possible to create a nicely colored HTML version of the theory that will look like [this](https://isabelle.in.tum.de/dist/library/HOL/HOL-Word/Word.html).
Execute the following command:

```console
$ make html
```

Generated HTML files will be created in a separate directory, the path to which will be printed on the screen.

