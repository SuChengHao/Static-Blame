# Static Blame

Warning: The project is not yet fully ready for open source, and although all code files are available, it does not yet have a complete interface for human use. It is full of Workarounds, such as absolute paths, bad variable names and inefficient functions. And, the documentation is not ready yet.

It currently exists only as support material for our thesis and is used to demonstrate our work.

## Description
Static Blame is a static analysis tool designed for the Grift language. For now, this project is a fork of [Grift repository](https://github.com/Gradual-Typing/Grift/tree/pldi19) with additional Static Blame files.

## What we have done and Code Structure:
1. The analysis tool, located in [src/static_blame](src/static_blame)
    1. the type flow generation process located in [src/static_blame/type_flow_generation.rkt](src/static_blame/type_flow_generation.rkt)
    2. the solver located in [src/static_blame/type_flow.rkt](src/static_blame/type_flow.rkt)
    3. basic definitions in [src/static_blame/refinement.rkt](src/static_blame/refinement.rkt)
    4. interface for scripts located in [src/static_blame/flow_analysis.rkt](src/static_blame/flow_analysis.rkt)
2. Test scripts, located in [src/static_blame/test](src/static_blame/test)
    1. Mutation analysis in [src/static_blame/test/mutate.rkt](src/static_blame/test/mutate.rkt)
    2. Main scripts in [src/static_blame/test/script.rkt](src/static_blame/test/script.rkt)
3. Test data, which you can use to re-generate main results.
    1. RQ1 in [final report](grift-exp/final report.csv)
    2. RQ2 in [configuration test](grift-exp/configuration test.csv) and [size_test](grift-exp/size test.csv)
    3. Plot facilities in [main.py](grift-exp/main.py)

## Reproduction of evaluation results
Make sure that you have installed `numpy` `pandas` and `matplotlib` in your python environment, and run main.py in the experimental directory.
```shell
cd grift-exp
python3 main.py
```
And every data in the paper will output to the standard output and pictures will be shown.
I recommend running it with [pycharm](https://www.jetbrains.com/pycharm)

