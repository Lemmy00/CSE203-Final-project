(*              THIS IS OT THE FINAL VERSION OF THE PROJECT             *)
(*          THE LAST FEW EXERCISES WILL BE UPLOADED ON TUESDAY          *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrbool List.


Set Implicit Arguments.

Axiom todo : forall {A}, A.
Ltac todo := by apply: todo.

(* ==================================================================== *)
(* This template contains incomplete definitions that you have to       *)
(* fill. We always used the keyword `Definition` for all of them but    *)
(* you are free to change for a `Fixpoint` or an `Inductive`.           *)
(*                                                                      *)
(* If needed, it is perfectly fine to add intermediate definitions and  *)
(* local lemmas.                                                        *)

(* ==================================================================== *)
(* In this project, we are going to develop and prove correct an        *)
(* algorithm for deciding the membership of a word w.r.t. a given       *)
(* regular language - all these terms are going to be defined below     *)

(* This project lies in the domain of *formal languages*. The study     *)
(* of formal languages is a branch of theoretical computer science and  *)
(* is about that is interested in the purely syntactical aspects of     *)
(* of languages and as applications in different domains, ranging from  *)
(* the definition of  the grammar of programming languages to the field *)
(* of automated translation.                                            *)

(* As with natural languages, we first need to fix an alphabet. In our  *)
(* case, we are simply going to declare a type `A : Type` - i.e. we     *)
(* will use the same alphabet for all the formal languages we are going *)
(* to study. Inhabitants of `A` are called `letters`.                   *)

Parameter (A : Type).

(* -------------------------------------------------------------------- *)
(* A `word` is then simply a finite sequence of letters of `A`. We      *)
(* denote by A* the set of words over `A`. In Coq, we are going to      *)
(* represent words as lists whose elements are inhabitants of `A`. This *)
(* naturally leads to the following definition:                         *)

Notation word := (list A).

(* -------------------------------------------------------------------- *)
(* You can get an overview of the List library at the following URL:    *)
(* https://coq.inria.fr/distrib/current/stdlib/Coq.Lists.List.html      *)

(* -------------------------------------------------------------------- *)
(* In this setting, a `language` is simply a subset of A*. Assuming     *)
(* that `x` & `y` are letters of A, we can define the following         *)
(* languages:                                                           *)
(*                                                                      *)
(*  - the empty language: `L = ∅`;                                      *)
(*                                                                      *)
(*  - the language that contains only the empty word ε (i.e. the only   *)
(*    (word of length 0): L = {ε}`;                                     *)
(*                                                                      *)
(*  - the language that contains all the words solely composed of the   *)
(*    letter `x`: L = { ε, x, xx, xxx, ... } = { xⁿ | n ∈ ℕ } (here,    *)
(*    xⁿ stands for the word x…x, where x is repeated n times);         *)
(*                                                                      *)
(*  - the language that contains all the words of the form xⁿyⁿ:        *)
(*    L = { xⁿyⁿ | n ∈ ℕ };                                             *)
(*                                                                      *)
(*  - if we assume that A contains the letter '[' & ']', we can         *)
(*    define the language of well-balanced words for '[' & ']':         *)
(*    L = { w ∈ { [, ] }* | s.t. P(w) && Q(w) }, where                  *)
(*      - P(w) = any prefix of w contain no more ]'s then ['s           *)
(*      - Q(w) = the number of ['s and ]'s of w are equal.              *)

(* --------------------------------------------------------------------      *)
(* We can also combine languages to form other languages. For example,       *)
(* if L and G are languages, we can define:                                  *)
(*                                                                           *)
(*  - the union of L & G            L ∪ G                                    *)
(*  - the concatenation of L & G    { w1 · w2 | w1 ∈ L, w2 ∈ G }             *)
(*  - the intersection of L & G     L ∩ G                                    *)
(*  - the complement of L           A* \ L                                   *)
(*  - the Kleene closure of L       L* = { w_1 ... w_n | n \in ℕ, w_i ∈ L }  *)
(*  - the mirror of L               rev(L) = { rev(w) | w ∈ L }              *)

(* -------------------------------------------------------------------- *)
(* To define languages in Coq, we need a way to represent subsets       *)
(* of A*, i.e. subsets of the set of `word`'s. To that end, we are      *)
(* going to represent a set using its indicator function. (We remind    *)
(* that, given a subset F of an ambient set E, the indicator function   *)
(* of F is the function f_E from E to { ⊤, ⊥ } s.t.                     *)
(*                                                                      *)
(*                     f_E(x) = ⊤ iff x ∈ E                             *)

(* In Coq, the codomain of its indicator function is going to be a      *)
(* proposition: given a function `F : E -> Prop`, we say that x belongs *)
(* to `x` iff `f x` holds.                                              *)

Notation language := (word -> Prop).

(* -------------------------------------------------------------------- *)
(* From now use, we assume that L, G, H denote languages, x, y denote   *)
(* letters and that and w denotes a word.                               *)

Implicit Types (L G H : language) (x y : A) (w : word).

(* -------------------------------------------------------------------- *)
(* From there, we can define the following languages                    *)

(* The empty language: no words belong to it.                           *)
(* (its indicator function always return `False`)                       *)
Definition lang0 : language :=
  fun w => False.

(* The language that only contains the empty word.                      *)
Definition lang1 : language :=
  fun w => w = nil.

(* Q1. We now ask you to define the following languages                 *)

(*  Given a word `w0`, the language that only contains the word `w0`.   *)
Definition langW w0 : language :=
  fun w => w = w0.

(* Given a sequence `ws` of words, the language that contains all the   *)
(* the words `ws` and only these words.                                 *)
Definition langF (ws : list word) : language :=
  fun w => (In w ws).

(* Given a letter `x`, the language that only contains the letter `x`   *)
(* seen as a word of length 1.                                          *)
Definition langA x : language :=
  fun w => w = (cons x nil).

(* The union of the two languages `L` and `G`.                          *)
Definition langU L G : language :=
  fun w => (L w) \/ (G w).

(* The intersection of the two languages `L` and `G`.                   *)
Definition langI L G : language :=
  fun w => (L w) /\ (G w).

(* The concatenation of the two languages `L` and `G`.                  *)
Definition langS L G : language :=
  fun w => (exists w1 w2 : word, ( w1 ++ w2 = w) /\ (L w1) /\ (G w2)).


(* The Kleene closure of the language `L`                               *)
Inductive langK L : language :=
|wnill : langK L nil
|winL w : L w -> langK L w
|cnct w1 w2 : langK L w1 -> langK L w2 -> langK L (w1 ++ w2).

(* The mirror of the language `L` (You can use the `rev`, that reversed *)
(* a list, from the standard library. *)
Definition langM L : language :=
  fun w => L (rev w).

(* -------------------------------------------------------------------- *)
(* Given two languages, we will consider `L` & `G` equal iff they       *)
(* contain the same words:                                              *)

Definition eqL L G := forall w, L w <-> G w.

Infix "=L" := eqL (at level 90).

(* Q2. Prove the following equivalances:                                *)

Lemma concat0L L : langS lang0 L =L lang0.
Proof.
move=> w.
split; unfold langS; unfold lang0; try done.
move=> [w1 [w2 [h [Contradition h1]]]].
done.
Qed.

Lemma concatL0 L : langS L lang0 =L lang0.
Proof.
move=> w.
split; unfold langS; unfold lang0; try done.
move=> [w1 [w2 [h [h1 Contradition]]]].
done.
Qed.

Lemma concat1L L : langS lang1 L =L L.
Proof.
move => w.
split; unfold langS; unfold lang1.
+move=> [w1 [w2 [h [nil Lw]]]].
 rewrite nil in h.
 simpl in h.
 rewrite h in Lw.
 done.
+move => Lw.
 exists nil. exists w.
 done.
Qed.

Lemma concatL1 L : langS L lang1 =L L.
Proof.
move => w.
split; unfold langS; unfold lang1.
+move=> [w1 [w2 [h [Lw nil]]]].
 rewrite nil in h.
 rewrite (app_nil_r w1) in h.
 rewrite h in Lw. done.
+move => Lw.
 exists w. exists nil.
 split; try done.
 apply (app_nil_r w).
Qed.


Lemma concatA L G H : langS (langS L G) H =L langS L (langS G H).
Proof.
move => w.
split; unfold langS.
+move => [w1 [w2 [h [[w3 [w4 [h1 [Lw3 Gw4] Hw2]]]]]]].
 exists w3. exists (w4 ++ w2).
 split.
 *rewrite <-h1 in h.
  rewrite <- h. 
  apply app_assoc.
 *split; try done.
  exists w4. exists w2.
  done.
+move => [w1 [w2 [h [Lw1 [w3 [w4 [h1 [Gw3 Hw4]]]]]]]].
 exists (w1 ++ w3). exists w4.
 split.
 *rewrite <-h1 in h.
  rewrite <- h. symmetry.
  apply app_assoc.
 *split; try done.
  exists w1. exists w3. 
  done.
Qed.

Lemma unionC L G : langU L G =L langU G L.
Proof.
move => w.
unfold langU.
split; move => [h1 | h2].
+right. done.
+left. done.
+right. done.
+left. done.
Qed.

Lemma interC L G : langI L G =L langI G L.
Proof.
move => w.
unfold langI.
split; move => [h1  h2]; split; done.
Qed.

Lemma langKK L : langK (langK L) =L langK L.
Proof.
move => w.
split; move => h; induction h; try done; try apply wnill.
 + apply cnct; done.
 + apply winL.
   apply winL.
   done.
 + apply winL.
   apply cnct; done.
Qed.

(* Note that, since languages are represented as indicator functions    *)
(* over `Prop`, we cannot assess that `L =L G` implies `L = G`.         *)

(* ==================================================================== *)
(*                          REGULAR LANGUAGES                           *)

(* We are now interested in a subclass of languages called "regular     *)
(* languages": a language `L` is said to be regular iff one of the      *)
(* following holds:                                                     *)
(*                                                                      *)
(*  - L = ∅ or L = {ε} or L = {x} for some x ∈ A ;                      *)
(*  - L = L1 ∪ L2 for L1, L2 regular languages ;                        *)
(*  - L = L1 · L2 for L1, L2 regular languages ;                        *)
(*  - L = G* for G a regular language.                                  *)

(* This kind of inductive definitions can be encoded in Coq using       *)
(* an inductive predicate `regular : language -> Prop` s.t.             *)
(*                                                                      *)
(*             L is regular iff `regular L` holds                       *)

(* Q3. complete the following definition of the predicate `regular`:    *)

Inductive regular : language -> Prop :=
  (* Any language equivalent to a regular language is regular *)
| REq L G of regular L & G =L L : regular G

  (* The empty language is regular *)
| REmpty : regular lang0
| REmptyW : regular lang1
| ROneW : forall x, regular (langA x)
| RUnion L1 L2 of regular L1 & regular L2 : regular (langU L1 L2)
| RConc L1 L2 of regular L1 & regular L2 : regular (langS L1 L2)
| RKleene L of regular L : regular (langK L).

(* -------------------------------------------------------------------- *)
(* Q4. prove that `langW w` is regular.                                 *)
Lemma regularW w : regular (langW w).
Proof.
induction w.
+move: REmptyW.
 unfold lang1.
 unfold langW.
 done.
+move: (ROneW a).
 move => h1.
 move: (RConc h1 IHw).
 move => h2.
 apply (REq h2).
 move => w1.
 unfold langW.
 unfold langS.
 unfold langA.
 split. move => h3.
 exists (cons a nil). exists w.
 split. 
 *symmetry.
  rewrite h3. done.
 *split; done.
 *move => [w2 [w3 [h3 [h4 h5]]]].
  rewrite h4 in h3. 
  rewrite h5 in h3.
  done.
Qed.


(* -------------------------------------------------------------------- *)
(* Q5. prove that `langM L` is regular, given that L is regular.        *)

Lemma aux_lemma L : forall w, langK L w -> langK (langM L) (rev w).
Proof.
move => w h. 
induction h.
+apply wnill.
+apply winL. 
 unfold langM.
 rewrite rev_involutive.
 done.
+rewrite rev_app_distr. by apply cnct.
Qed.

Lemma regularM L : regular L -> regular (langM L).
Proof.
move=> h.
induction h.
+unfold langM.
 apply REq with (langM L); try done.
 unfold langM.
 split; apply H.
+unfold langM. apply REmpty.
+unfold langM. 
 apply REq with (fun w => lang1 w).
 *apply REmptyW.
 *split; unfold lang1;induction w; try done.
  move => h.
  simpl in h.
  symmetry in h.
  apply app_cons_not_nil in h. done.
+apply (REq (ROneW x)).
 move => w. 
 unfold langM. 
 unfold langA.
 split; move => h.
  move: (rev_involutive w).
  move => h1.
  rewrite h in h1.
  done.
 *rewrite h. 
  done.
+apply (REq (RUnion IHh1 IHh2)). 
 move => w. 
 unfold langM. 
 unfold langU. 
 done.
+apply (REq (RConc IHh2 IHh1)). 
 move => w. 
 unfold langM.
 unfold langS.
 split; move => [w1 [w2 h]]. destruct h; destruct H0.
 exists (rev w2).
 exists (rev w1).
 split.
 *symmetry in H.
  symmetry.
  apply rev_eq_app. done.
 *split.
  -move: (rev_involutive w2).
   move => rev_h.
   rewrite rev_h.
   done.
  -move: (rev_involutive w1).
   move => rev_h.
   rewrite rev_h.
   done.
  *exists (rev w2).
   exists (rev w1).
   split; destruct h; destruct H0.
   -symmetry in H.
    symmetry.
    apply rev_eq_app.
    move: (rev_involutive w).
    move => h.
    rewrite h.
    done.
   -split; done.
+apply (REq (RKleene IHh)).
 move => w.
 split; move => h1.
 *unfold langM in h1. 
  move: (aux_lemma h1).
  move => h2.
  rewrite rev_involutive in h2. 
  done.
 *induction h1; unfold langM.
  -apply wnill.
  -apply winL. 
   done.
  -rewrite rev_app_distr. 
   apply cnct; done.
Qed.


(* ==================================================================== *)
(*                        REGULAR EXPRESSIONS                           *)

(* Related to regular languages is the notion of regular expressions.   *)
(* A regular expression is a formal, syntactic expression that can      *)
(* latter be interpreted as a regular language. Regular expressions are *)
(* pervasive in computer science, e.g. for searching for some text in   *)
(* a file, as it is possible with the `grep` command line tool.         *)
(*                                                                      *)
(* For instance, the command:                                           *)
(*                                                                      *)
(*    grep -E 'ab*a' foo.txt                                            *)
(*                                                                      *)
(* is going to print all the lines of `foo.txt` that contains a word    *)
(* of the form ab⋯ba (where the letter b can be repeated 0, 1 or more   *)
(* time. I.e., grep is going to find all the lines of `foo.txt` that    *)
(* contains a word that belongs in the formal language:                 *)
(*                                                                      *)
(*    L = { abⁿa | n ∈ ℕ }                                              *)
(*                                                                      *)
(* If you need to convince yourself that L is regular, note that:       *)
(*                                                                      *)
(*    L = { a } ∪ { b }* ∪ { a }                                        *)
(*                                                                      *)
(* In some sense, a regular expression is just a compact way to         *)
(* represent a regular language, and its definition is going to be      *)
(* close to the one of regular languages.                               *)
(*                                                                      *)
(* A regular expression is either:                                      *)
(*                                                                      *)
(*  - the constant ∅ or the constant ε or one letter from A             *)
(*  - the disjunction r1 | r2 of two regular expressions                *)
(*  - the concatenation r1 · r2 of two regular expressions              *)
(*  - the Kleene r* of some regular expression                          *)

(* We can represent regular expressions as a inductive type in Coq.     *)

(* Q6. complete the following definition:                               *)

Inductive regexp : Type :=
| RE_Empty : regexp
| RE_Void  : regexp
| RE_Atom  : A -> regexp
| RE_Dis   : regexp -> regexp -> regexp
| RE_Conct : regexp -> regexp -> regexp
| RE_Kleene : regexp -> regexp

  (* TO BE COMPLETED *)
.

Implicit Types (r : regexp).

(* We now have to formally related regular expressions to regular       *)
(* languages. For that purpose, we are going to interpret a regular     *)
(* expression as a languages. If r is a regular expression, then we     *)
(* denote by language [r] as follows:                                   *)
(*                                                                      *)
(*   - [∅]       = ∅                                                    *)
(*   - [ε]       = ε                                                    *)
(*   - [a]       = { a } for a ∈ A                                      *)
(*   - [r₁ ∪ r₂] = [r₁] ∪ [r₂]                                          *)
(*   - [r₁ · r₂] = [r₁] · [r₂]                                          *)
(*   - [r*]      = [r]*                                                 *)

(* Q7. implement the Coq counterpart of the above definition:           *)

Fixpoint interp (r : regexp) {struct r} : language :=
  match r with
  | RE_Empty => lang0
  | RE_Void => lang1
  | RE_Atom A => langW (cons A nil)
  | RE_Dis r1 r2 => (langU (interp r1) (interp r2))
  | RE_Conct r1 r2 => (langS (interp r1) (interp r2))
  | RE_Kleene r1 => (langK (interp r1))
  end.

(* Q8. show that the interpretation of a regular expression is a        *)
(*     regular language:                                                *)

Lemma regular_regexp r : regular (interp r).
Proof.
induction r; simpl.
+apply REmpty.
+apply REmptyW.
+apply ROneW.
+apply RUnion; done.
+apply RConc; done.
+apply RKleene; done.
Qed.

(* Q9. show that any regular language can be interpreted as a           *)
(*     regular expression:                                              *)


Lemma equal_langU (L1 L2 G1 G2: language) : L1 =L L2 -> G1 =L G2 -> langU L1 G1 =L langU L2 G2.
Proof.
unfold eqL. 
move => h1 h2 w.
unfold langU.
move: (h1 w).
move => [h3 h4]. 
move: (h2 w).
move => [h5 h6].
split; case.
+left. 
 apply (h3 a).
+right.
 apply (h5 b).
+left. 
 apply (h4 a). 
+right.
 apply (h6 b).
Qed.

Lemma equal_langS (L1 L2 G1 G2: language) : L1 =L L2 -> G1 =L G2 -> langS L1 G1 =L langS L2 G2.
Proof.
unfold eqL. 
move => h1 h2 w. 
unfold langS.
split; move => [w1 [w2 h]]; destruct h; destruct H0; 
exists w1; exists w2; split; try done; split; try apply h1; try apply h2; done.
Qed.

Lemma equal_langK L G: L =L G -> langK L =L langK G.
Proof.
unfold eqL. 
move => h w0.
split; move => h1; induction h1; try apply wnill.
+apply winL. 
 move: (h w) => [h2 h3]. 
 apply (h2 H).
+apply cnct; done. 
+apply winL. 
 move: (h w) => [h2 h3]. 
 apply (h3 H).
+apply cnct; done.
Qed.

Lemma regexp_regular L : regular L -> exists r, L =L interp r.
Proof.
move => h. induction h.
+move: IHh => [r h1]. 
 exists r.
 split.
 *move => h2.
  apply h1. 
  apply H.
  done.
 *move => h2.
  apply H.
  apply h1.
  done.
+exists RE_Empty. done.
+exists RE_Void. done.
+exists (RE_Atom x). done.
+move: IHh1.
 move => [r1 h3]. 
 move: IHh2. 
 move =>[r2 h4]. 
 exists (RE_Dis r1 r2).
 simpl. 
 apply equal_langU; done.
+move: IHh1.
 move => [r1 h3]. 
 move: IHh2. 
 move =>[r2 h4]. 
 exists (RE_Conct r1 r2).
 simpl. 
 apply equal_langS; done.
+move: IHh.
 move => [r1 h3].
 exists (RE_Kleene r1).
 simpl.
 apply equal_langK.
 done.
Qed.

(* Of course, it may happen that two regular expressions represent      *)
(* the same language: r1 ~ r2 iff [r1] = [r2].                          *)

(* Q10. write a binary predicate eqR : regexp -> regexp -> Prop s.t.    *)
(*      eqR r1 r2 iff r1 and r2 are equivalent regexp.                  *)

Definition eqR (r1 r2 : regexp) : Prop := (interp r1) =L (interp r2).

Infix "~" := eqR (at level 90).

(* Q11. state and prove the following regexp equivalence:               *)
(*           (a|b)* ~ ( a*b* )*                                         *)

Lemma langKlangU_LR: forall a b w1 w2, (langK (interp a) w1) -> (langK (interp b) w2) -> 
    (langK (langU (interp a) (interp b)) w1) /\ (langK (langU (interp a) (interp b)) w2).
Proof.

split.
induction H. 
apply wnill. 
apply winL. 
by left.
apply cnct. 
apply IHlangK1. 
apply IHlangK2.
induction H0. 
apply wnill. 
apply winL. 
by right.
apply cnct. 
apply IHlangK1. 
apply IHlangK2.
Qed.

Lemma kl_or_eq_kl_kls: forall (a b: regexp),
                    (RE_Kleene (RE_Dis a b)) ~ 
                    (RE_Kleene (RE_Conct (RE_Kleene a) (RE_Kleene b))).
Proof.
split.

+simpl.
move=>h0.
induction h0.

-apply wnill.

-apply winL.
unfold langS. 
unfold langU in H.
destruct H.
exists w, nil.
split. 
apply app_nil_r.
split.
apply winL; done.
apply wnill.
exists nil, w.
split.
done.
split.
apply wnill.
apply winL;done.

-by apply cnct.

+simpl.
move=> h.
induction h.

-apply wnill.

-move: H=> [w1 [w2 [eq [h1 h2]]]].
rewrite -eq.
apply cnct.
apply langKlangU_LR with a b w1 w2 in h1. 
move: h1 => [h1l h1r]. 
apply h1l.
done.
apply langKlangU_LR with a b w1 w2 in h2. 
move: h2 => [h2l h2r]. 
apply h2r.
done.

-by apply cnct.
Qed.

(* ==================================================================== *)
(*                          REGEXP MATCHING                             *)

(* We now want to write a algorithm for deciding if a given word `w`    *)
(* matches a regular expression `r`, i.e. for deciding wether `w ∈ [r]` *)
(*                                                                      *)
(* For that purpose, we are going to use Brzozowski's derivatives.      *)
(*                                                                      *)
(* The idea of the algorithm is the following:                          *)
(*                                                                      *)
(* Given a letter `x` and an regular expression `r`, the Brzozowski's   *)
(* derivatives of `x` w.r.t. `r` is a regular expression x⁻¹·r s.t.     *)
(*                                                                      *)
(*    x · w ∈ [r] ⇔ w ∈ [x⁻¹·r]                                         *)
(*                                                                      *)
(* Assuming that we can compute a Brzozowski's derivative for any       *)
(* letter `x` and regular expression `r`, one can check that a word `w` *)
(* matches a regexp `r` as follows:                                     *)
(*                                                                      *)
(*   - if w = x · w' for some letter x and word w', we recursively      *)
(*     check that `w` matches `x⁻¹·r`; otherwise                        *)
(*   - if w = ε, then we directly check that [r] contains the empty     *)
(*     word - a property that is deciable.                              *)

(* Q12. write a nullity test `contains0` : regexp -> bool s.t.          *)
(*                                                                      *)
(*      ∀ r, contains0 r ⇔ ε ∈ [e]                                      *)

Fixpoint contains0 (r : regexp) : bool := 
  match r with
  | RE_Empty => false
  | RE_Void => true
  | RE_Atom _ => false
  | RE_Dis r1 r2 => contains0 r1 || contains0 r2
  | RE_Conct r1 r2 => contains0 r1 && contains0 r2
  | RE_Kleene r => true
  end.

(* Q13. prove that your definition of `contains0` is correct:           *)

Lemma contains0_ok r : contains0 r <-> interp r nil.
Proof. 
split.
move => h1.
induction r; try done.
simpl.
simpl in h1.
unfold langU.
case a: (contains0 r1).
left.
apply IHr1.
done.
right.
case b: (contains0 r2).
apply IHr2.
done.
apply IHr2.
rewrite b.
rewrite a in h1.
rewrite b in h1.
done.
simpl in h1.
simpl.

unfold langS.
exists nil, nil.
simpl.
split.
done.
case a: (contains0 r1);case b: (contains0 r2);
try split; try apply IHr1; try apply IHr2; 
try rewrite a; try rewrite b; try rewrite a in h1; try rewrite b in h1;
try simpl in h1; try apply h1; try done.
simpl.
apply wnill.
move => h1.
induction r;simpl;try done.
simpl in h1.
unfold langU in h1.
move: h1 => [for_r1|for_r2];try intuition.
simpl in h1.
move: h1 => [w1 [w2 [H [a b]]]].

apply app_eq_nil in H.
move: H=>[H1 H2].
rewrite H1 in a.
rewrite H2 in b.
rewrite IHr1.
done.
rewrite IHr2; try done.
Qed.

(* We give below the definition of the Brzozowski's derivative:         *)
(*                                                                      *)
(*   - x⁻¹ · x         = ε                                              *)
(*   - x⁻¹ · y         = ∅ if x ≠ y                                     *)
(*   - x⁻¹ · ε         = ∅                                              *)
(*   - x⁻¹ · ∅         = ∅                                              *)
(*   - x⁻¹ · (r₁ | r₂) = (x⁻¹ · r₁) | (x⁻¹ · r₂)                        *)
(*   - x⁻¹ · (r₁ · r₂) = (x⁻¹ · r₁) · r₂ | E(r₁) · (x⁻¹ · r₂)           *)
(*   - x⁻¹ · r*        = (x⁻¹ · r) · r*                                 *)
(*                                                                      *)
(* where E(r) = ε if ε ∈ [r] & E(r) = ∅ otherwise.                      *)

(* Q14. write a function `Brzozowski` that computes a Brzozowski's      *)
(*      derivative as defined above.                                    *)
(*                                                                      *)
(* For that purpose, you may need to have a decidable equality over     *)
(* `A`. The parameter `Aeq` along with the axioms `Aeq_dec` give        *)
(* you such a decidable equality.                                       *)

Parameter Aeq : A -> A -> bool.

(* Here, `Aeq x y` has to be read as `Aeq x y = true`                   *)
Axiom Aeq_dec : forall (x y : A), Aeq x y <-> x = y.

Fixpoint Brzozowski (x : A) (r : regexp) : regexp :=
  match r with
  | RE_Atom y => if (Aeq x y) then RE_Void else RE_Empty
  | RE_Void => RE_Empty
  | RE_Empty => RE_Empty
  | RE_Dis r1 r2 => RE_Dis (Brzozowski x r1) (Brzozowski x r2)
  | RE_Conct r1 r2 => if (contains0 r1) 
    then RE_Dis (RE_Conct (Brzozowski x r1) r2) (RE_Conct RE_Void (Brzozowski x r2))
    else RE_Dis (RE_Conct (Brzozowski x r1) r2) (RE_Conct RE_Empty (Brzozowski x r2))
  | RE_Kleene r => RE_Conct (Brzozowski x r) (RE_Kleene r)
  end.

(* Q15. write a function `rmatch` s.t. `rmatch r w` checks wether a     *)
(*      word `w` matches a given regular expression `r`.                *)

Fixpoint rmatch (r : regexp) (w : word) : bool := 
  match w with
  | nil => contains0 r
  | cons x w => rmatch (Brzozowski x r) w
  end.

(* Q16. show that the `Brzozowski` function is correct.                 *)

Lemma Brzozowski_correct (x : A) (w : word) (r : regexp) :
  interp (Brzozowski x r) w -> interp r (x :: w).
Proof. todo. Qed.

(* Q17. show that `rmatch` is correct.                                  *)

Lemma rmatch_correct (r : regexp) (w : word):
  rmatch r w -> interp r w.
Proof. todo. Qed.

(* Q18. (HARD - OPTIONAL) show that `rmatch` is complete.               *)

Lemma rmatch_complete (r : regexp) (w : word):
  interp r w -> rmatch r w.
Proof. todo. Qed.
