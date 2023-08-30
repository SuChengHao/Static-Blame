## Dynamizer ##

Dynamizer is a command line tool that produces all valid less precisely-typed
variants of a valid explicitly-typed program in
[Grift](https://github.com/Gradual-Typing/Grift). The output is valid Grift
source code files commented with how much they are dynamically-typed.  Dynamizer
is primarily used for benchmarking the different implementations of gradual
typing in the Grift project.

I am still looking into extending the dynamizer to other gradually typed
languages such as reticulated python.

## Compiling

The too is implemented in Haskell and can be built using [stack](https://docs.haskellstack.org/en/stable/README/).

```
stack build
```

## Usage
The dynamizer has several modes of execution, a few examples are provided. However, it writes the generated configurations to disk as valid grift source files in a directory of the same name as the input program and located right beside that program.

Let's grab a Grift program for demo:
```bash
wget https://raw.githubusercontent.com/Gradual-Typing/benchmarks/master/src/static/matmult/single/matmult.grift 
```

All configurations will be written to disk, 859963392 in this case, if no optional parameter is specified.
```console
$ stack exec dynamizer -- --fine matmult.grift
Number of all configurations: 859963392
Number of all type nodes: 33
```

To generate 1000 configurations, 100 from 0-10% statically typed bin, another 100 from 10-20%, and so on.
```console
$ stack exec dynamizer -- --fine --configurations-count 100 --bins 10  matmult.grift
Number of all configurations: 859963392
Number of all type nodes: 33
Number of requested configurations: 1000
```
