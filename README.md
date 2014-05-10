# th-alpha

Alpha equivalence for TH's `Exp` type. That is, check whether two expressions
are the same modulo the renaming of bound variables:

    >>> areExpAEq [| \x -> x |] [| \y -> y |]
    True
    >>> areExpAEq [| let x = 5 in x |] [| let y = 5 in y |]
    True

And that's about it, really. Useful if you're generating code and want to test
the result: in those cases correctness is usually only defined up to alpha
equivalence.
