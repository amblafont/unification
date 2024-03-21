We thank the referees for their useful comments and suggestions.

We would like to start by replying Reviewer 3's comment that our work is 
light-weighted on the theoretical side. First, we are happy that we managed to present this work so that it looks easy. To us, the main theoretical contribution is the categorical semantics of higher-order pattern unification, as computing equalisers in suitable Lawvere theories. We are not aware of any direct semantic account in the litterature in this style, and it somehow explains the similarity between higher-order pattern unification and first-order unification algorithms, which has been noticed many times in the litterature.
This is why we chose to focus on explaining the semantics in the main body of the papers and leave the examples in the appendices. However, we agree that it would be helful to sketch at least one other example than untyped lambda-calculus (for example, Miller's original setting based on normalised simply-typed lambda-calculus). If accepted, we will integrate such an example.

Our theoretical investigation led to a single parameterisable algorithm that applies in many settings (this is where the full generality of GB-signatures pays off, to answer reviewer 1).





DETAILED RESPONSE
-------------------
  
We give detailed answers to the questions in each of the reviews below (TODO).
  
Review 1 
-----------------

> 176: this motivates avoiding the use of "some kind of error monad", but then Maybe (which is canonically "some kind of error monad") is used anyway.  So it makes it sound like you are doing something different here, rather than something uncontroversial and fairly standard in pure Haskell/Agda settings.  Or at least the difference was not clear to me.

We do use Maybe, but not in the place that is usally expected in a pure functional setting. Indeed, the result type of the unification algorithm is not embedded into a Maybe type (see Figure 3). Moreover, the semantics of our algorithm is a complete function rather than a partial function: the keypoint is that what is usually interpreted as failure can in fact be interpreted as a fully fledged coequaliser (Section 6.2).

 > 220- regarding the extra requirements that metavariable arguments be distinct, > I would thin kin Agda one could enforce this by requiring the mappings m => n > to be injective rather than arbitrary finite maps from [1...n] to [1...m], 
 > right?  Why not do this?

 We could indeed implement this restriction (and we should if we want to mechanise the proof of correctness, that we plan to do in the future). We preferred to make the implementation lighter and leave out some required properties out of the implementation (such as the existence of connected limits).


 > 353: why leave n implicit and not other things?  because usually this judgment > is used with n=0, or because it's always easy to figure out what n should be?

 We choose to emphasize on metacontexts and leave the variable context implicit to alleviate the notation. This judgement is not usually used when n=0.

 > 408: "then obviously there is no unifier" - there hasn't really been any 
 > discussion so far of the formal statement of the unification problem so to 
 > make it clearer why this is obvious here it might help to point out that in 
 > HOU/HOPU the substitutions for the metavariables have to be closed - ie no 
 > dependences on bound variables other than those explicitly given by the 
 > arguments.

 > 633: is the long double arrow here between alpha o and alpha (o {x}) the same > kind of arrow as in x : a => b or in line 626??

 They are not the same: the double long arrow denotes a renaming between two metacontexts (Notation 2.10) while the short one denotes a renaming  between two natural numbers (see below Remark 2.1).

Review 2
---------

- how can we adapt our work to the dependently typed setting?

We plan to investigate Uemura's notion of representable map categories which seems to play a role analogous to that of Lawvere theories, but for dependently typed syntax.

- are there any known ways to modify the paper's contribution to capture some equational theories?

We were thinking of devising a version of Hur and Fiore's notion of equational systems [1] compatible with unification. We thank the reviewer for suggesting looking at pra monads: this looks like a very interesting path to explore! Let us finally note that our setting can handle the case where there are normal forms and they can be specified by a GB-signature (as it is the case for simply-typed lambda calculus modulo beta/eta, detailed in the Appendix). 

[1] Marcelo P. Fiore, Chung-Kil Hur, Equational Systems and Free Constructions, ICALP 2007

