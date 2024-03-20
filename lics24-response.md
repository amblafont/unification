We thank the referees for their useful comments and suggestions.

We would like to start by replying Reviewer 3's comment that our work is 
light-weighted on the theoretical side. To us, the main theoretical contribution is the categorical semantics of higher-order pattern unification, as computing equalisers in suitable Lawvere theories. We are not aware of any direct semantic account in the litterature in this style, and it somehow explains the similarity between higher-order pattern unification and first-order unification algorithms, which has been noticed many times in the litterature.
This is why we chose to focus on explaining the semantics in the main body of the papers and leave the examples in the appendices. However, we agree that it would be helful for the reader to sketch at least one other example than untyped lambda-calculus (for example, Miller's original setting based on normalised simply-typed lambda-calculus). If accepted, we will integrate such an example.

Our theoretical investigation led to a single parameterisable algorithm that applies in many settings (this is where the full generality of GB-signatures pays off, to answer reviewer 1).





DETAILED RESPONSE
-------------------
  
We give detailed answers to the questions in each of the reviews below (TODO).
  
Review 1 
-----------------

> 170:  in/around 170 I wondered what about types/  It seems this is possible to accommodate as a special case of the general framework in section 2.2. But little is said explicitly.  I think the paper would be improved generally by mentioning the (even if there are few details) especially for simply-typed lambda / beta normal eta long terms since these are often taken as the starting point for HOPU.

> 176: this motivates avoiding the use of "some kind of error monad", btu then Maybe (which is canonically "some kind of error monad" is used anyway.  So it makes it sound like you are doing something different here, rather than something uncontroversial and fairly standard in pure Haskell/Agda settings.  Or at least the difference was not clear to me.

 > 220- regarding the extra requirements that metavariable arguments be distinct, > I would thin kin Agda one could enforce this by requiring the mappings m => n > to be injective rather than arbitrary finite maps from [1...n] to [1...m], 
 > right?  Why not do this?

 Yes, we could, and we should if we want to mechanise the proof of correctness (that we plan to do in the future). We preferred to make the implementation more readable and leave out some required properties out of the implementation (such as the existence of connected limits).

 > 353: why leave n implicit and not other things?  because usually this judgment > is used with n=0, or because it's always easy to figure out what n should be?

 This n should be inferred.

 > 408: "then obviously there is no unifier" - there hasn't really been any 
 > discussion so far of the formal statement of the unification problem so to 
 > make it clearer why this is obvious here it might help to point out that in 
 > HOU/HOPU the substitutions for the metavariables have to be closed - ie no 
 > dependences on bound variables other than those explicitly given by the 
 > arguments.

 > 633: is the long double arrow here between alpha o and alpha (o {x}) the same > kind of arrow as in x : a => b or in line 626??

Review 2
---------

>  The paper mentions that generalised pattern unification capturing
dependently-typed LF-style signatures is future work for the author(s).
Could any details be provided about how the categorical semantics of such
unification algorithms may be described?

> Finitary endofunctors T : Cb → Cb on a presheaf category that preserve
connected limits are also known as parametric right adjoint (pra) endofunctors [Web07]. When T is also a cartesian monad, it comes with a
category of canonical arities [BMW12], which is a full subcategory of the
Kleisli category of T. I wonder if this setting would be appropriate to treat
pattern unification modulo an equational theory (by considering a general
pra monad on [A, Set] instead of the free monad considered in the current
paper). Perhaps some known examples of decidable unification modulo
theory can be captured in this setting?
More generally, are there any known ways to modify the paper’s contribution to capture some equational theories?
