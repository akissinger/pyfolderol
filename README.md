# What is this?

PyFolderol is a toy theorem prover, based loosely on Larry Paulson's `folderol` prover, as described in:

* [Designing a Theorem Prover](https://arxiv.org/abs/cs/9301110). Lawrence Paulson, 1990.

Thanks to structural pattern matching in Python 3.10, a lot of the code pretty closely resembles the original ML. In interests of keeping things simple, the whole prover is implemented in one Python file (approx. 500 LOC). It is essentially undocumented, but it should be understandable to anyone who has read the paper above. A couple of changes I made were:

* incorporating a slightly nicer parser, based on [Lark](https://github.com/lark-parser/lark).
* shifting some of the utility functions into methods on the `Term`, `Form`, and `Goal` classes.
* replacing the simple automated procedure with a single tactic `rule`, which takes an LK rule name and applies it to the first formula in the first goal that matches it.

This was mainly a learning exercise, with some of the code here possibly making its way into [Chyp](https://github.com/akissinger/chyp) at some point. However, if you find the code useful, feel free to use it.

