(** * Counter Example for Strong Pi injectivity in PTSe.
*)

Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import List.

Require Import base final_result.

(** Sorts ::= {u, v, v' , w ,w' } *)
Module Msorts <: term_sig.
Inductive iSorts : Set :=
 | U : iSorts
 | V : iSorts
 | V' : iSorts
 | W : iSorts
 | W': iSorts
 .

Definition Sorts := iSorts.
End Msorts.

(** Ax ::= { (u,v), (u,v'), (v,w) (v',w') } *)
Module Mpts <: pts_sig Msorts.
Import Msorts.
Inductive iAx : Sorts -> Sorts -> Prop :=
 | Ax0 : iAx U V
 | Ax1 : iAx U V'
 | Ax2 : iAx V W
 | Ax3 : iAx V' W'
.

(** Rel ::= { (w,w,w), (w',w',w'), (v,v,u), (v',v',u) } *)
Inductive iRel : Sorts -> Sorts -> Sorts -> Prop :=
 | Rel0 : iRel W W W
 | Rel1 : iRel W' W' W'
 | Rel2 : iRel V V U
 | Rel3 : iRel V' V' U.

Definition Ax := iAx.
Definition Rel := iRel.
End Mpts.


Module CE <: Theory Msorts Mpts.
Import Msorts Mpts. 
Include Theory Msorts Mpts.

Hint Constructors iAx iRel.
Hint Unfold Ax Rel.

Definition PTSe_PiInj := forall Γ A B C D u, Γ ⊢e Π(A),B = Π(C),D : !u -> exists s, exists t, Rel s t u /\
 Γ ⊢e A = C : !s /\ A::Γ ⊢e B = D : !t.

Definition D1 := (λ[!V],#0)·!U. (*  id_v · !u : coercion to force the type of this term to be ONLY !v *)
Lemma D1_ok : nil ⊢e D1 : !V.
change !V with !V[← !U]. unfold D1. econstructor.
econstructor. apply Rel0. eauto. constructor. intuition. econstructor. eauto.
constructor. eauto. exists !V.  intuition. eauto.
Qed.

Lemma D1_typ : forall T, nil ⊢e D1 : T -> T ≡ !V.
intros. apply PTS_equiv_PTSe in H.  unfold D1 in H. apply gen_app in H. destruct H as (A & B & ? & ? & ?).
apply gen_la in H0 as (s & t & u & D & h); decompose [and] h; clear h. apply PiInj in H0 as (? & ?).
apply gen_var in H4 as ( VV & ? & ?). destruct H7 as (VVV & ? & ?). inversion H8; subst; clear H8.
simpl in H4. apply Betac_trans with B [← !U]. trivial. change !V with !V[← !U]. eauto.
Qed.

Definition D2 := (λ[!V'],#0)·!U. (*  id_v' · !u : coercion to force the type of this term to be ONLY !v' *)
Lemma D2_ok : nil ⊢e D2 : !V'.
change !V' with !V'[← !U]. unfold D2. econstructor.
econstructor. apply Rel1. intuition. constructor. intuition. eauto. constructor. eauto.
exists !V'; intuition. eauto.
Qed.

Lemma D2_typ : forall T, nil ⊢e D2 : T -> T ≡ !V'.
intros. apply PTS_equiv_PTSe in H.  unfold D2 in H. apply gen_app in H. destruct H as (A & B & ? & ? & ?).
apply gen_la in H0 as (s & t & u & D & h); decompose [and] h; clear h. apply PiInj in H0 as (? & ?).
apply gen_var in H4 as ( VV & ? & ?). destruct H7 as (VVV & ? & ?).  inversion H8; subst; clear H8.
simpl in H4. apply Betac_trans with B[← !U]. trivial. change !V' with !V'[← !U]. eauto.
Qed.

Lemma ze_pi_eq : nil ⊢e Π(D1),!U = Π(D2),!U : !U.
apply cTrans with (Π(!U),!U). eapply cPi_eq. apply Rel2.
change !U with #0[← !U]; change !V with !V[← !U]. unfold D1.
eapply cBeta. apply Rel0. intuition. constructor. intuition. eauto.
constructor. eauto. exists !V; intuition. intuition. 
constructor. constructor. intuition. econstructor. apply D1_ok.

eapply cPi_eq. apply Rel3. apply cSym.
change !U with #0[← !U]; change !V' with !V'[← !U]. unfold D2.
eapply cBeta. apply Rel1. intuition. constructor; eauto.  constructor; eauto.
exists !V'; intuition. eauto.
constructor. constructor. intuition. eauto.
Qed.

Lemma Dom_ce : forall s, nil ⊢e D1 = D2 : !s -> False.
intros.
assert (nil ⊢e D1 : !s). apply left_reflexivity in H; trivial.
assert (nil ⊢e D2 : !s). apply right_reflexivity in H; trivial.
apply D1_typ in H0. apply D2_typ in H1. apply conv_sort in H0; subst.
apply conv_sort in H1; discriminate.
Qed.


Lemma PTSe_dont_have_PiInj :  ~ PTSe_PiInj .
intro. red in H.
destruct (H nil D1 !U D2 !U U ze_pi_eq) as (s & t & ? & ? & ?).
apply Dom_ce in H1.
trivial.
Qed.

End CE.
