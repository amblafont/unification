Generic pattern unification implemented in Agda (tested with v2.7.0.1, with standard library v2.1.1).

Contents:
- lib.lagda: some general purpose definitions and lemmas
- lc.lagda (~450 LoC): pattern unification for λ-calculus
- main.lagda (~300 LoC): generic pattern unification
- common.lagda (~175 LoC): Agda code shared verbatim between lc.lagda and main.lagda
- lcsig.agda: signature for λ-calculus
- systemF.agda (~800 LoC): signature for system F