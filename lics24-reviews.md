----------------------- REVIEW 1 ---------------------
SUBMISSION: 62
TITLE: Semantics of pattern unification
AUTHORS: Ambroise Lafont and Neelakantan Krishnaswami

----------- Overall evaluation -----------
SCORE: 1 (weak accept)
----- TEXT:
Summary

Higher-order pattern unification (HOPU) is a special case of higher-order unification (unification of lambda-calculus terms) in which restrictions are placed on the use of metavariables which ensure that unification is efficiently decidable and unitary (most general unifiers exist and are unique up to renaming).  As introduced by Miller, HOPU is a HOU problem in which metavariable occurrences are always of the form X y1 ... yn where y1...yn are distinct bound variables (i.e introduced by lambda-abstractions above the occurrence of X).

This paper proposes a generalization of HOPU with the following features:
1. Metavariables have arities rather than being thought of as having lambda-calculus types (thus, unification of untyped terms is accommodated).
2. Languages can be specified by binding signatures or generalizations thereof.
3.  Correctness of the general case is proved with respect to a semantics formulated via category theory, where certain steps of unification correspond to categorical constructions like (co)equalizer and pullback/pushout constructions
4. Unification algorithm fore generalized binding signatures/terms is parameterized by a small number of language-specific functions/proof obligations, such as providing the equalizer and pullback operations
5. Implementation in Agda using de Bruijn levels syntax - dependent types used to help keep various things straight but not to fully formalize correctness.

Evaluation

I do not have the background to fully assess/check the categorical semantics so limit my comments to the parts I am qualified to judge and proceed on the assumption that there are no major technical problems in the details I am not following.

With that caveat, my view of the paper is as follows.  It develops an interesting generalization of higher-order pattern unification which to some extent distills the higher-order pattern restriction to an essence that can be transferred to other settings, via the generalization of binding signatures in section 2.2.  However in its current form the paper is really dense even for someone familiar with HOU/HOPU.  The paper doesn't really ever explain what HOPU (in its classic/conventional form) really is nor how the formulation taken in this paper is equivalent - I believe it is but unless there's a similar treatment out there somewhere (that the paper should be citing) this needs a little more exposition.  Similarly, the extensive use of Agda and de Bruijn syntax in the first half of the paper and category theoretic notation in the second half sometimes makes the paper somewhat heavy going.  Finally the paper is a little short on motivation of and examples for the general case
 of generalized binding signatures, specifically, it is not clearly explained in the paper how various examples (detailed in the appendix) fit the framework and how the full generality of GB signatures pays off in terms of applications.

I think many of these issues could be addressed by relatively simple revisions to the paper (not affecting the technical content at all just the presentation and what is said in the main body vs appendix) if that is possible within the LICS review process.  Also, it is possible that to more specialized reviewers the significance and depth of the results would carry greater weight.  So overall I am weakly in favor of acceptance of the paper.

Detailed comments

41-65: this paragraph makes it sound like Dunfield and Krishnaswami  and Zhao et al. studied different type inference algorithms, but as far as I can see Zhao et al. set out to formalize Dunfield and Krishnaswami.  Maybe more could be said about why there isn't much reuse opportunity (if there isn't).  But also as far as I know (could be wrong) higher order *pattern* unification plays no role in these algorithms.

70: "as simple as innocuous"


170:  in/around 170 I wondered what about types/  It seems this is possible to accommodate as a special case of the general framework in section 2.2. But little is said explicitly.  I think the paper would be improved generally by mentioning the (even if there are few details) especially for simply-typed lambda / beta normal eta long terms since these are often taken as the starting point for HOPU.

170: also around this point it became clear to someone already familiar that you ar using de Bruijn syntax (levels not indices) but this should be said explicitly, and while it is pretty obvious to the PL-in-Agda community it is better not to self- limit the paper's audience to people that already know/guess this from context.

176: this motivates avoiding the use of "some kind of error monad", btu then Maybe (which is canonically "some kind of error monad" is used anyway.  So it makes it sound like you are doing something different here, rather than something uncontroversial and fairly standard in pure Haskell/Agda settings.  Or at least the difference was not clear to me.

220- regarding the extra requirements that metavariable arguments be distinct, I would thin kin Agda one could enforce this by requiring the mappings m => n to be injective rather than arbitrary finite maps from [1...n] to [1...m], right?  Why not do this?

243: might be worth noting that the m \in Gamma argument is "proof relevant", i.e. there could be several copies of m and the argument will take different values to refer to different ones (usually membership will essentially be a unary natural number index into the list).

263-280: even if technically you don't have to in Agda, it is not vert readable to me to say App. t u [sigma]t instead of (App. t u)[sigma]t, adding parentheses in this way to the various cases would help readability.

313: starting around here it seems there is a convention that x : m => n is a variable renaming (i.e.a  finite / injective map), I would find it helpful as a reminder that it's a more complex structure to write \vec{x} or \bar{x} or something

353: why leave n implicit and not other things?  because usually this judgment is used with n=0, or because it's always easy to figure out what n should be?

394: "keeps M but changes its arity to p" - this was a place where the at least superficial differences to conventional HOPU become clearer.  Conventionally one substitutes M with \lambda x1...xn. M' y1...yn where the mapping p is derived from the choices of x's and y's.  Changing M's type/arity requires making sure all other occurrences of M are so changed, which is fine here I think as long as the substitution and context management is done consistently

408: "then obviously there is no unifier" - there hasn't really been any discussion so far of the formal statement of the unification problem so to make it clearer why this is obvious here it might help to point out that in HOU/HOPU the substitutions for the metavariables have to be closed - ie no dependences on bound variables other than those explicitly given by the arguments.

468-476 it took me a while to unpack and follow the definitions of the various ->? judgments, which are not mentioned anywhere in the text either (though partly due to slightly less familiarity with Agda record syntax)

633: is the long double arrow here between alpha o and alpha (o {x}) the same kind of arrow as in x : a => b or in line 626??

721: it might help presentationally to say right away how Aczel's binding signatures are an instance of GB-signatures (example 2.8), and to give (ideally a simple) example of a non-discrete category - as the motivation for generalizing to GB signatures in this way is not clear. 

820: "convenient define"

Lemma 3.6: capitalize "metacontexts"


Defnition 3.15: "is said *to be* pattern-friendly"

1076: missing period at end of sentence

1364: In addition to Cheney's early work on relating nominal and higher-order pattern unification, Levy and Villaret studied the relationship later (see reference)

1426: Reference 27 is missing information about where/how published

Reference

Jordi Levy and Mateu Villaret. 2012. Nominal Unification from a Higher-Order Perspective. ACM Trans. Comput. Logic 13, 2, Article 10 (April 2012), 31 pages. https://doi.org/10.1145/2159531.2159532


----------------------- REVIEW 2 ---------------------
SUBMISSION: 62
TITLE: Semantics of pattern unification
AUTHORS: Ambroise Lafont and Neelakantan Krishnaswami

----------- Overall evaluation -----------
SCORE: 2 (accept)
----- TEXT:
Evaluation:

The paper under review clearly provides an interesting contribution to the theory of higher-order unification. Grouping different versions of the same pattern unification algorithm together using a “unified” category-theoretic semantics is an important step towards understanding more complex unification problems. The definitions of GB-signature and the mathematical proofs are concise and elegant.

The paper also provides avenues for future research. In particular, the semantics of the generalised algorithm lead one to believe that similar techniques can be used to reason about pattern unification problems for dependently typed signatures.

Therefore I recommend that it be accepted to LICS 2024.

(see attached PDF for detailed review)

<This review contains an attachment, which can be
downloaded from EasyChair.>

----------------------- REVIEW 3 ---------------------
SUBMISSION: 62
TITLE: Semantics of pattern unification
AUTHORS: Ambroise Lafont and Neelakantan Krishnaswami

----------- Overall evaluation -----------
SCORE: 1 (weak accept)
----- TEXT:
** SUMMARY **

This paper gives a semantics-driven formulation of the unification phase in type inference. It is based on the syntax with binding signatures and meta-variables and their presheaf-based semantics (originating from the seminal work by Fiore, Plotkin and Turi, with further refinement by Hamana and others). As a result, we obtain a generic form of the unification algorithm which can be systematically instantiated to various languages.

** EVALUATION **

This work gives a nice example of applying semantic ideas and frameworks to an important problem in programming languages practice. Thus, I buy it as a good semantic-engineering paper. The presentation is well-organized; it begins with concrete syntax and algorithms and then proceeds to the semantic proof of the correctness.

On the other hand, this work is rather light-weighted: it does not give much new theoretical insight, just presents a very cleaver use of known techniques, and the outcome is not too surprising. I think this lightness is nice as an engineering paper, but not necessarily so in a conference like LICS. I feel that this work would be more suitable for some PL conferences (like POPL and ICFP). 

** COMMENTS **

- page 9, line 952 (and many places after that):
I think MCon_\bot(S) is MCon(S)_\bot .