# What is this?

PyFolderol is a toy theorem prover, based loosely on Larry Paulson's `folderol` prover, as described in:

* [Designing a Theorem Prover](https://arxiv.org/abs/cs/9301110). Lawrence Paulson, 1990.

Thanks to structural pattern matching in Python 3.10, a lot of the code pretty closely resembles the original ML. In interests of keeping things simple, the whole prover is implemented in one Python file (approx. 500 LOC). It is essentially undocumented, but it should be understandable to anyone who has read the paper above. A couple of changes I made were:

* incorporating a slightly nicer parser, based on [Lark](https://github.com/lark-parser/lark).
* shifting some of the utility functions into methods on the `Term`, `Form`, and `Goal` classes.
* replacing the simple automated procedure with a single tactic `rule`, which takes an LK rule name and applies it to the first formula in the first goal that matches it.

This was mainly a learning exercise, with some of the code here possibly making its way into [Chyp](https://github.com/akissinger/chyp) at some point. However, if you find the code useful, feel free to use it.

# Usage

To use the prover, construct a `Proof` object with a goal. Call `Proof.rule` to update the state with a reverse application of one of the rules of the sequent calculus [LK](https://en.wikipedia.org/wiki/Sequent_calculus#The_system_LK), using the variant described in Paulson's paper. The rules acting on the left part of the sequent are called `andL`, `orL`, `impliesL`, `iffL`, `allL`, `existsL`, and similarly the rules acting on the right are called `andR`, `orR`, `impliesR`, `iffR`, `allR`, `existsR`.


At any point, printing the proof object will show the open goals. Here's a simple example:

```python
from folderol import *
pf = Proof(parse_goal('forall x . Q(x) and P(x) |- forall x . P(x) and Q(x)'))
print(pf)

pf.rule('allR'); print(pf)
pf.rule('allL'); print(pf)
pf.rule('andR'); print(pf)
pf.rule('andL'); print(pf)
pf.rule('andL'); print(pf)
```


This will give the following output:

    1 goal:
      ∀x.(Q(x) ∧ P(x)) ⊢ ∀x.(P(x) ∧ Q(x))


    1 goal:
      ∀x.(Q(x) ∧ P(x)) ⊢ (P(x0) ∧ Q(x0))


    1 goal:
      (Q(?x1) ∧ P(?x1)), ∀x.(Q(x) ∧ P(x)) ⊢ (P(x0) ∧ Q(x0))


    2 goals:
      (Q(?x1) ∧ P(?x1)), ∀x.(Q(x) ∧ P(x)) ⊢ P(x0)
      (Q(?x1) ∧ P(?x1)), ∀x.(Q(x) ∧ P(x)) ⊢ Q(x0)


    1 goal:
      (Q(x0) ∧ P(x0)), ∀x.(Q(x) ∧ P(x)) ⊢ Q(x0)


    qed
