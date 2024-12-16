# Formalizing "Abstracting Extensible Data Types" in Agda

This is an attempt to formalize "Abstracting Extensible Data Types" by Morris and McKinna in the Agda programming language.

The implementation consists of 3 files:
- `Language/SystemF.lagda.md` is the extended System F language that Rose gets translated into
- `Language/Rose.lagda.md` consists of the typing derivation and rules of the main language
- `Language/Properties.lagda.md` encodes the main lemmas and proofs of the paper

## Challenges

All the lemmas given in `Properties.lagda.md` do not have  finished proofs (in fact, some are not even correctly formed). I think this stems from some of the underlying problems in the formalism given in `Rose.lagda.md`.
Among the few are:

- The indexing of rows in the System F implementation assumes zero-based indexing, but the paper indexes from 1; this has propagated through the entire formalism of `Rose`!
Fixing it isn't easily done as the Agda implementation uses `Fin` and `Vec` depndent types.
- A harder problem is the underlying, implicit assumption that the type system is Hindley-Milner based. Thus unification must eventually come into the picture, and I have not much experience with encoding that in Agda. 
This problem can be clearly seen in `lemma8-1` where row variables are part of the proof.
- Assumptions were made on some notations in the paper, particularly on the author's use of the free variable `fv` function that appears to be polymorphic on its inputs and the number of inputs it accepts.
- Finally, while the derivation is polymorphic over the row theory it accepts, the implementation uses Figure 8 in the paper for its row theory. That is, we assume a trivial row theory in the implementation. However, the resulting implementation is messy because it encodes the roles as computations producing System F terms instead of data types.