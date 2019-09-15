# plcc-ch2-long-division

Formal proof of correctness of long division algorithm as appearing in PLCC Chapter 2, modelled within an Imp variant

## How to build

### Using CoqIDE 8.9.x on a Mac

Fire up your terminal, change directory to your local copy of this repo and run `coq_makefile -f _CoqProject -o Makefile`, then open any vernacular file from this repo in your CoqIDE and select `Compile > Make`.

*N.B. The terminal workaround is necessary for generating the correct Makefile due to [coq/coq#10736](https://github.com/coq/coq/issues/10736).*

## Spoiler Alert

In the end of Chapter 2 of [Program Logics for Certified Compilers (PLCC)](https://vst.cs.princeton.edu/download/PLCC-to-chapter-3.pdf), the reader is advised to work through the steps of the proof involving the correctness of the long division algorithm shown here (or consult a detailed proof referenced by the book). You are advised not to peek at the contents of this repo until you have at least made an attempt at proving it yourself, though it is not mandatory to do so.

## Credits

The long division algorithm is taken from a [free excerpt of PLCC](https://vst.cs.princeton.edu/download/PLCC-to-chapter-3.pdf) while the toy programming language used in this repo is a variant of Imp in [Software Foundations](https://softwarefoundations.cis.upenn.edu), an excellent resource for learning Coq.

## License

A signification portion of work in this repo is adapted from the [Software Foundations](https://softwarefoundations.cis.upenn.edu) series, whose license terms are reproduced verbatim below as per the license terms:

Copyright (c) 2019

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
