(** * Beta reduction for annotated terms 
As for the usual terms, we extend the definition of [Beta] to handle the
two additional annotations. Since we want to prove that the typed version
of the reduction is confluent, we don't care to prove it for this version.*)
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import Le.
Require Import Gt.
Require Import Plus.
Require Import Minus.
Require Import Bool.
Require Import base.
Require Import term.

Module Type red_mod (X:term_sig) (TM:term_mod X).
Import TM.
Reserved Notation " A → B " (at level 80).

Inductive Beta : Term -> Term -> Prop :=
 | Beta_head : forall A M N K L , (λ[ A ], M)·(K,L) N → M [← N]
 | Beta_red1 : forall M M' N A B, M → M' -> M·(A,B) N  → M'·(A,B) N
 | Beta_red2 : forall M N N' A B, N → N' -> M·(A,B) N  → M ·(A,B) N'
 | Beta_red3 : forall M N A B B', B → B' -> M·(A,B) N  → M ·(A,B') N
 | Beta_red4 : forall M N A A' B, A → A' -> M·(A,B) N  → M ·(A',B) N
 | Beta_lam  : forall A M M'    , M → M' -> λ[A],M     → λ[A ],M'
 | Beta_lam2 : forall A A' M    , A → A' -> λ[A],M     → λ[A'],M
 | Beta_pi   : forall A B B'    , B → B' -> Π(A),B     → Π(A ),B'
 | Beta_pi2  : forall A A' B    , A → A' -> Π(A),B     → Π(A'),B
where "M → N" := (Beta M N) : Typ_scope.

Reserved Notation " A →→ B" (at level 80).

Inductive Betas : Term -> Term -> Prop :=
 | Betas_refl  : forall M    , M →→ M
 | Betas_Beta  : forall M N  , M → N  -> M →→ N
 | Betas_trans : forall M N P, M →→ N -> N →→ P -> M →→ P
where "A →→ B" := (Betas A B) : Typ_scope.

Hint Constructors Beta Betas.

Lemma Betas_App : forall M M' N N' A A' B B', M →→ M' -> N →→ N' ->  A →→ A' -> B →→ B' -> 
  M·(A,B)N →→ M'·(A',B')N'.
assert (forall a b c A B , b →→ c ->  a·(A,B)b →→ a·(A,B)c).
induction 1; eauto. 
assert (forall a b c A B, b→→c -> b·(A,B) a →→ c·(A,B) a).
induction 1; eauto.
assert (forall a b A B B', B →→ B' -> a·(A,B) b →→ a·(A,B') b).
induction 1; eauto.
assert (forall a b A A' B, A →→ A' -> a·(A,B) b →→ a·(A',B) b).
induction 1; eauto.
intros. eapply Betas_trans. apply H. apply H4. eapply Betas_trans. apply H0. apply H3. eauto.
Qed.

Hint Resolve Betas_App.

Lemma Betas_La : forall A A' M M', A →→ A' -> M →→ M' -> λ[A],M →→ λ[A'],M'.
assert (forall a b c , a →→ b -> λ[c],  a →→ λ[c], b).
induction 1; eauto.
assert (forall a b c, a →→ b -> λ[a], c →→ λ[b], c).
induction 1; eauto.
eauto.
Qed.


Hint Resolve Betas_La.


Lemma Betas_Pi : forall A A' B B', A →→ A' -> B →→ B' -> Π(A),B →→ Π(A'),B'.
assert (forall a b c , a →→ b -> Π (c), a →→ Π(c), b).
induction 1; eauto.
assert (forall a b c, a →→ b -> Π(a), c →→ Π(b), c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betas_Pi.

Reserved Notation "M →' N" (at level 80).

Inductive Betap : Term -> Term -> Prop :=
 | Betap_sort : forall s                  , !s →' !s
 | Betap_var  : forall v                  , #v →' #v
 | Betap_lam  : forall A A' M M'          , A →' A' -> M →' M' -> λ[A],M →' λ[A'],M'
 | Betap_pi   : forall A A' B B'          , A →' A' -> B →' B' -> Π(A),B →' Π(A'),B'
 | Betap_App  : forall M M' N N' A A' B B', M →' M' -> N →' N' -> A →' A' -> B →' B' ->
    M ·(A,B) N →' M'·(A',B') N'
 | Betap_head : forall A M M' N N' K L    , M →' M' -> N →' N' -> (λ[A],M)·(K,L) N →' M'[← N']
where "A →' B" := (Betap A B ) : Typ_scope.

Reserved Notation "M  →→' N" (at level 80).

Inductive Betaps : Term -> Term -> Prop :=
 | Betaps_intro : forall M N  , M →'  N -> M →→' N
 | Betaps_trans : forall M N P, M →→' N -> N →→' P -> M →→' P
where "M →→' N" := (Betaps M N) : Typ_scope.


Hint Constructors Betap Betaps. 

Lemma Betap_to_Betas : forall M N, M →' N -> M →→ N.
induction 1; intuition.
eapply Betas_trans. eapply Betas_App. eapply Betas_La. apply Betas_refl.
apply IHBetap1. apply IHBetap2. apply Betas_refl. apply Betas_refl.
constructor. econstructor.
Qed.

Lemma Betaps_to_Betas : forall M N, M →→' N -> M →→ N.
induction 1; eauto. apply Betap_to_Betas in H; trivial.
Qed.

Lemma Betap_refl : forall M, M →' M.
induction M; intuition.
Qed.

Hint Resolve Betap_refl.

Lemma Betaps_Beta_closure : forall M N,  M → N -> M →' N.
induction 1; intuition.
Qed.

Lemma Betaps_Betas_closure :  forall M N, M →→ N -> M →→' N.
induction 1. intuition.
apply Betaps_Beta_closure in  H; intuition.
eauto.
Qed.

End red_mod.
