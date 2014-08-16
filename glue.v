(** * Validity of Annotations
In this file, we prove all the tools we need to show  that a welltyped judgment
of PTS can be annotated in a valid judgement of PTS_{atr}. With this, we give
a validity to the annotation system we chose.*)
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt Plus Minus.

Require Import base.
Require Import term.
Require Import env red.
Require Import typ_annot.
Require Import List.
Require Import ut_term ut_env ut_red.
Require Import strip.

Module Type glue_mod  (X:term_sig) (Y:pts_sig X) (TM:term_mod X) (EM: env_mod X TM) (RM: red_mod X TM)
                                            (UTM:ut_term_mod X) (UEM: ut_env_mod X UTM) (URM: ut_red_mod X UTM).
 Import X Y UTM UEM URM TM EM RM.
 Include (strip_mod X UTM TM UEM EM).
 Include (PTS_ATR_mod X Y TM EM RM).

Open Scope Typ_scope.

(** This lemma gives some partial information about a term, when its types are
not convertible, it will be usefull to prove that annotation in application
are safe.*)
Lemma weak_type_shape : forall Γ M N A, Γ ⊢ M ▹ N : A -> forall P B, Γ ⊢ M ▹ P : B ->
 Γ ⊢ A ≡' B \/ (exists U,exists V, Γ ⊢ M ▹ λ[U],V : A /\ Γ ⊢ M ▹ λ[U],V : B) \/
 (exists s, Γ ⊢ M ▹ !s : A /\ Γ ⊢ M ▹ !s : B) \/
 (exists U, exists V, Γ ⊢ M ▹ Π(U),V : A /\ Γ ⊢ M ▹ Π(U),V : B).
induction 1; intros.
apply pgen_var in H1. destruct H1 as ( _ & A' & ? & ? ).
left. replace A with A'. intuition. eapply fun_item_lift. apply H1. trivial.
(**)
apply pgen_sort in H1. destruct H1 as ( _ & t & ? & ? ).
right; right; left. exists s1; split.
eauto. destruct H2. subst; eauto. eapply typ_pcompat; eauto.
(**)
clear IHtyp1 IHtyp2. apply pgen_pi in H2 as (A'' & B'' & s & t & u & h); decompose [and] h; clear h.
right; right; right. exists A'; exists B'; split. eapply typ_pi; eauto.
destruct H7. subst. apply typ_pi with s t; trivial.
eapply relocate. apply H4. apply H0. eapply relocate. apply H3. apply H1. apply typ_pcompat with !u; intuition.
apply typ_pi with s t; trivial. eapply relocate. apply H4. apply H0. eapply relocate. apply H3. apply H1.
(**)
clear IHtyp1 IHtyp2 IHtyp3.
right; left. apply pgen_la in H3 as (A'' & M'' & D & s & t &u & h); decompose [and] h; clear h.
exists A'; exists M'; split. eapply typ_la. apply H. trivial. apply H1. trivial.
apply typ_pcompat with (Π(A),D). eapply typ_la. apply H3. eapply relocate. apply H5. apply H0.
apply H6. eapply relocate. apply H4. apply H2. trivial.
(**)
apply pgen_app in H4 as (C & C' &  D' & N'' & s & t & u & h). decompose [and] h; clear h.
left; trivial.
(**)
apply pgen_app in H7. destruct H7 as (C & C' & D' & N'' & s & t & u & h). decompose [and] h; clear h.
left; trivial.
(**)
destruct (IHtyp1 P B0 H1) as [ | [ | [ | ] ] ]. left; eauto.
destruct H2 as (U & V & ? & ?). right; left. exists U; exists V; split. eapply typ_pcompat with A; eauto. trivial.
destruct H2 as ( t & ? & ?). right; right; left. exists t; split. eapply typ_pcompat with A; eauto. trivial.
destruct H2 as (U & V & ? & ?). right; right; right. exists U; exists V; split. eapply typ_pcompat with A; eauto. trivial.
(**)
destruct (IHtyp1 P B0 H1) as [ | [ | [ | ] ] ]. left; eauto.
destruct H2 as (U & V & ? & ?). right; left. exists U; exists V; split. eapply typ_pcompat with B; eauto. trivial.
destruct H2 as ( t & ? & ?). right; right; left. exists t; split. eapply typ_pcompat with B; eauto. trivial.
destruct H2 as (U & V & ? & ?). right; right; right. exists U; exists V; split. eapply typ_pcompat with B; eauto. trivial.
Qed.

Lemma peq_not_Pi_sort : forall Γ A B S, ~(Γ ⊢ Π(A),B ≡' !S).
intros; intro. apply Confluence in H as (Z & ? & ?  &? & ?).
apply Sort_Reds in H0 as ( -> & ?& ?).
apply Pi_Reds in H as ( A' & B' & ? & ? & ? & ? & ? & _ ). discriminate.
Qed.

(** First step to prove the annotation valid: we need to find a path between two
different annotated version of a same "stripped" term. We don't care that [A] is not
equal to [B] here, since this results will mainly  be used for types, so both
[A] and [B] will be sorts, which is enough to build an equality.*)
(** This is the main point of proving annotations valid, and we need the full
power of confluence and type exchange to be able to prove it.*)

Lemma ErasedTermConfluence : forall M N Γ A B, strip M = strip N ->
  Γ ⊢ M ▹ M : A -> Γ ⊢ N ▹ N : B ->
  exists P,  Γ ⊢ M ▹▹ P : A /\ Γ ⊢ N ▹▹ P : B.
induction M; intros.
(**)
destruct N; simpl in H; try discriminate. injection H; intros; subst; clear H.
apply red_refl_lt in H1. apply red_refl_lt in H0. exists #v0; intuition.
(**)
destruct N; simpl in H; try discriminate. injection H; intros; subst; clear H.
apply red_refl_lt in H1. apply red_refl_lt in H0. exists !s0; intuition.
(**)
destruct N; simpl in H; try discriminate. injection H; intros; subst; clear H.
rename M1 into P. rename M4 into Q. rename M2 into An. rename M3 into D.
rename N1 into P'. rename N4 into Q'. rename N2 into An'. rename N3 into E.
apply pgen_app in H0 as (C & C1 & D' & Q1 & s1 & t1  & u1 & h). decompose [and] h ; clear h.
apply pgen_app in H1 as (C' & C'1 & E' & Q'1 & s2 & t2  & u2 & h). decompose [and] h ; clear h.
assert (exists PP, Γ ⊢ P ▹ PP : Π(C),D). destruct H8. destruct H8 as (P'' & ? & ? & ?). subst. exists P''; trivial.
destruct H8 as (U0 & K & K' & T & T' & ? & -> & ? & _). exists (La C1 T'). econstructor. subst. apply H. trivial. apply red_refl_lt in H0; apply H0.
trivial.
assert (exists PP', Γ ⊢ P' ▹ PP' : Π(C'),E). destruct H13. destruct H13 as (P'' & ? & ? & ?). subst. exists P''; trivial.
destruct H13 as (U0 & K & K' & T & T' & ? & -> & ?  & _ ). exists (La C'1 T'). subst. econstructor. apply H1. trivial.
apply red_refl_lt in H7; apply H7. trivial.
destruct H12 as (PP & ?). destruct H14 as (PP' & ?).
apply red_refl_lt in H5. apply red_refl_lt in H10.
destruct (IHM4 Q' Γ C C' H2 H5 H10) as (RQ & ? & ? ). clear IHM4.
apply red_refl_lt in H12. apply red_refl_lt in H14.
destruct (IHM1 P' Γ (Pi C D) (Pi C' E) H3 H12 H14) as (RP & ? & ? ). clear IHM1. clear IHM2 IHM3.
destruct (weak_type_shape Γ RP RP (Π(C),D)) with (P := RP) (B := Π(C'),E) as [ | [ | [ ] ] ].
apply reds_refl_rt in H17; trivial. apply reds_refl_rt in H18; trivial.
  (**  Phase 1 : Pi C D == Pi C' E **)
destruct (PiInj Γ C D C' E H19) as (? & ?).
  (** 1 / 4 **)
destruct H8.  destruct H8 as (? & _ & ? &  _ ). subst. clear x.  destruct H13.  destruct H8 as (? & _ & ? &  _ ). clear x. subst.
apply Confluence in H21 as (Z & d1 & d2 & ? & ?). destruct (Confluence Γ C C' H20) as (ZA & d3 & d4 & ? & ?).
rename H8 into HH8. assert (H8 : C::Γ ⊢ D ▹▹ Z : !t1). eapply typ_reds_relocate. apply HH8. apply red_refl_lt in H0; apply H0. clear HH8.
rename H13 into HH13. assert (H13 : C'::Γ ⊢ E ▹▹ Z : !t2). eapply typ_reds_relocate.  eapply conv_in_env_reds. apply HH13. eauto.
apply red_refl_lt in H7; apply  H7. clear HH13.
rename H21 into HH21. assert (H21 : Γ ⊢ C ▹▹ ZA : !s1). eapply typ_reds_relocate. apply HH21. apply red_refl_lt in H4; apply H4. clear HH21.
rename H22 into HH22. assert (H22 : Γ ⊢ C' ▹▹ ZA : !s2). eapply typ_reds_relocate. apply HH22. apply red_refl_lt in H9; apply H9. clear HH22.
clear d1 d2 d3 d4.
exists (App RP ZA Z RQ); split.
apply reds_typ_pcompat with (D [ ← Q]); trivial. eapply reds_App. trivial. trivial. apply H21. apply H8.
apply reds_typ_pcompat with (E [ ← Q']); trivial.  eapply reds_App. trivial. trivial. apply H22. apply H13.
 (**  2 / 4 **)
destruct H8 as (G0 & G & G' & ? & ? & ? & _ & _ & _ & HH2 & HH1 & HH0). clear x x0. subst.
apply Confluence in H21 as (Z & d1 & d2 & ? & ?). destruct (Confluence Γ C G) as (ZA & d3 & d4 & ? & ?). apply reds_to_conv in HH1. apply reds_to_conv in HH2.
apply typ_peq_trans with C'; intuition. apply typ_peq_trans with G0; intuition.
rename H8 into HH8. assert (H8 : C::Γ ⊢ D ▹▹ Z : !t1). eapply typ_reds_relocate. apply HH8. apply red_refl_lt in H0; apply H0. clear HH8.
rename H13 into HH13. assert (H13 : C'::Γ ⊢ E ▹▹ Z : !t2). eapply typ_reds_relocate.  eapply conv_in_env_reds. apply HH13. eauto.
apply red_refl_lt in H7; apply  H7. clear HH13.
rename H21 into HH21. assert (H21 : Γ ⊢ C ▹▹ ZA : !s1). eapply typ_reds_relocate. apply HH21. apply red_refl_lt in H4; apply H4. clear HH21.
rename H22 into HH22. assert (H22 : Γ ⊢ G ▹▹ ZA : !s2). eapply typ_reds_relocate. apply HH22. apply red_refl_lt in HH0; apply HH0. clear HH22.
clear d1 d2 d3 d4.
assert(HEQ1: Γ ⊢ C' ≡' G). apply reds_to_conv in HH1. apply reds_to_conv in HH2. eauto.
assert (HEQ2: Γ ⊢ Π(C'),E ≡' Π(G),E). apply typ_peq_trans with (Π(G0),E). apply typ_peq_sym.
apply reds_to_conv with u2. eapply reds_Pi. apply HH1.  constructor. eapply conv_in_env. apply red_refl_lt in H7; apply H7. eauto. trivial.
apply reds_to_conv with u2. eapply reds_Pi. apply HH2.  constructor. eapply conv_in_env. apply red_refl_lt in H7; apply H7. eauto. trivial.
exists (App RP ZA Z RQ); split.
apply reds_typ_pcompat with (D [ ← Q]); trivial. eapply reds_App. trivial. trivial. apply H21. apply H8.
apply reds_typ_pcompat with (E [ ← Q']); trivial.  eapply reds_App. apply reds_typ_pcompat with (Π(C'),E); trivial.  apply reds_typ_pcompat with C'; trivial.
apply H22. eapply conv_in_env_reds. apply H13. eauto.
  (**  3 / 4 **)
destruct H8 as (G0 & G & G' & ? & ? & ? & _ & _ & _ & HH2 & HH1 & HH0). subst. clear x x0. destruct H13.
destruct H8 as ( ? & _ & ? & _ ). subst. clear x.
assert(HEQ1: Γ ⊢ C' ≡' G). apply reds_to_conv in HH1. apply reds_to_conv in HH2. eauto.
assert (HEQ3: Γ ⊢ C ≡' G). eauto.
assert (HEQ2: Γ ⊢ Π(C),D ≡' Π(G),D). apply typ_peq_trans with (Π(G0),D). apply typ_peq_sym.
apply reds_to_conv with u1. eapply reds_Pi. apply HH1.  constructor. eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto. trivial.
apply reds_to_conv with u1. eapply reds_Pi. apply HH2.  constructor. eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto. trivial.
apply Confluence in H21 as (Z & d1 & d2 & ? & ?). destruct (Confluence Γ G C') as (ZA & d3 & d4 & ? & ?). intuition.
rename H8 into HH8. assert (H8 : G::Γ ⊢ D ▹▹ Z : !t1). eapply typ_reds_relocate. eapply conv_in_env_reds. apply HH8. eauto. eapply conv_in_env.
apply red_refl_lt in H0; apply  H0. eauto. clear HH8.
rename H13 into HH13. assert (H13 : C'::Γ ⊢ E ▹▹ Z : !t2). eapply typ_reds_relocate.  eapply conv_in_env_reds. apply HH13. eauto.
apply red_refl_lt in H7; apply  H7. clear HH13.
rename H21 into HH21. assert (H21 : Γ ⊢ G ▹▹ ZA : !s1). eapply typ_reds_relocate. apply HH21. apply reds_refl_rt in HH2; apply HH2. clear HH21.
rename H22 into HH22. assert (H22 : Γ ⊢ C' ▹▹ ZA : !s2). eapply typ_reds_relocate. apply HH22. apply red_refl_lt in H9; apply H9. clear HH22.
clear d1 d2 d3 d4.
exists (App RP ZA Z RQ); split.
apply reds_typ_pcompat with (D [ ← Q]); trivial. eapply reds_App. apply reds_typ_pcompat with (Π(C),D); trivial. apply reds_typ_pcompat with C; trivial. apply H21. apply H8.
apply reds_typ_pcompat with (E [ ← Q']); trivial.  eapply reds_App. trivial. trivial. apply H22. apply H13.
   (**  4 / 4 **)
destruct H8 as (F0 & F & F' & ? & ? & ? & _ & _ & _  & HH5 & HH4 & HH3). subst. clear x x0.
assert (HEQ1 : Γ ⊢ G ≡' C). apply reds_to_conv in HH1. apply reds_to_conv in HH2. eauto.
assert (HEQ2 : Γ ⊢ F ≡' C'). apply reds_to_conv in HH4. apply reds_to_conv in HH5. eauto.
assert (HEQ3 : Γ ⊢ G ≡' F). eauto.
assert (HEQ4: Γ ⊢ Π(C),D ≡' Π(G),D). apply typ_peq_trans with (Π(G0),D). apply typ_peq_sym.
apply reds_to_conv with u1. eapply reds_Pi. apply HH1.  constructor. eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto. trivial.
apply reds_to_conv with u1. eapply reds_Pi. apply HH2.  constructor. eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto. trivial.
assert (HEQ5: Γ ⊢ Π(C'),E ≡' Π(F),E). apply typ_peq_trans with (Π(F0),E). apply typ_peq_sym.
apply reds_to_conv with u2. eapply reds_Pi. apply HH4.  constructor. eapply conv_in_env. apply red_refl_lt in H7; apply H7. eauto. trivial.
apply reds_to_conv with u2. eapply reds_Pi. apply HH5.  constructor. eapply conv_in_env. apply red_refl_lt in H7; apply H7. eauto. trivial.
apply Confluence in H21 as (Z & d1 & d2 & ? & ?). destruct (Confluence Γ G F HEQ3) as (ZA & d3 & d4 & ? & ?).
rename H8 into HH8. assert (H8 : G::Γ ⊢ D ▹▹ Z : !t1). eapply typ_reds_relocate. eapply conv_in_env_reds. apply HH8. eauto. eapply conv_in_env.
apply red_refl_lt in H0; apply  H0. eauto. clear HH8.
rename H13 into HH13. assert (H13 : F::Γ ⊢ E ▹▹ Z : !t2). eapply typ_reds_relocate.  eapply conv_in_env_reds. apply HH13. eauto. eapply conv_in_env.
apply red_refl_lt in H7; apply H7. eauto. clear HH13.
rename H21 into HH21. assert (H21 : Γ ⊢ G ▹▹ ZA : !s1). eapply typ_reds_relocate. apply HH21. apply reds_refl_rt in HH2; apply HH2. clear HH21.
rename H22 into HH22. assert (H22 : Γ ⊢ F ▹▹ ZA : !s2). eapply typ_reds_relocate. apply HH22.  apply reds_refl_rt in HH5; apply HH5. clear HH22.
clear d1 d2 d3 d4.
exists (App RP ZA Z RQ); split.
apply reds_typ_pcompat with (D [ ← Q]); trivial. eapply reds_App. apply reds_typ_pcompat with (Π(C),D); trivial. apply reds_typ_pcompat with C; intuition. apply H21.  apply H8.
apply reds_typ_pcompat with (E [ ← Q']); trivial.  eapply reds_App. apply reds_typ_pcompat with (Π(C'),E); trivial. apply reds_typ_pcompat with C'; intuition. apply H22. apply H13.
  (** Phase 2 : RP -> λ **)
destruct H19 as (U & V & ? & ?).
destruct (pgen_la Γ U V (λ[U],V) (Π(C),D)) as (U' & V' & K & s & t & u & h).
apply red_refl_rt in H19; trivial. decompose [and] h; clear h. injection H25; intros; subst; clear H25.
destruct (pgen_la Γ U' V' (λ[U'],V') (Π(C'),E)) as (U'' & V'' & L & s' & t' & u' & h).
apply red_refl_rt in H20; trivial. decompose [and] h; clear h. injection H30; intros; subst; clear H30.
destruct (PiInj Γ U'' K C D H27) as ( ? & ?). destruct (PiInj Γ U'' L C' E H32) as ( ? & ?). exists (V''[← RQ]).
  (** 1 / 4 **)
destruct H8.  destruct H8 as (? & _ & ? &  _ ). subst. clear x.  destruct H13.  destruct H8 as (? & _ & ? &  _ ). clear x. subst.
split. apply reds_typ_pcompat with (D [ ← Q]); trivial.
destruct (Confluence (U''::Γ) K D H31) as (ZB & a & b & ? & ?). destruct (Confluence Γ U'' C H30) as (ZA & c & d & ? & ?).
rename H35 into HH35. assert (H35: Γ ⊢ U'' ▹▹ ZA : !s). eapply typ_reds_relocate. apply HH35. apply H23. clear HH35.
rename H36 into HH36. assert (H36: Γ ⊢ C ▹▹ ZA : !s1). eapply typ_reds_relocate. apply HH36. apply red_refl_lt in H4; apply H4. clear HH36.
rename H8 into HH8. assert (H8 : U''::Γ ⊢ K ▹▹ ZB : !t). eapply typ_reds_relocate. apply HH8. apply H24. clear HH8.
rename H13 into HH13. assert (H13 : C::Γ ⊢ D ▹▹ ZB : !t1). eapply typ_reds_relocate. eapply conv_in_env_reds. apply HH13. eauto.
apply red_refl_lt in H0; apply H0. clear HH13.
clear a b c d.
eapply typ_reds_trans. eapply reds_App. eapply typ_reds_trans. apply H17. constructor. apply H19.  constructor; apply red_refl_lt in H5; apply H5.  constructor; apply red_refl_lt in H4; apply H4.
constructor. apply red_refl_lt in H0; apply H0. eapply typ_reds_trans. eapply reds_App. constructor; apply red_refl_rt in H19; apply H19.  apply H15. apply H36. apply H13. constructor.
apply typ_pcompat with (ZB [← RQ]). eapply typ_beta. apply H21. apply H23. eapply reds_refl_rt. apply H35. constructor. apply H23.
trivial. apply reds_refl_rt in H8; apply H8. apply typ_pcompat with K. trivial. eapply reds_to_conv; apply H8. apply typ_pcompat with C. apply reds_refl_rt in H15; trivial. eauto.
apply typ_peq_sym. apply reds_to_conv with t1. change !t1 with (!t1[← Q]). eapply reds_subst_gen. apply H13.
apply reds_typ_pcompat with C; eauto. apply reds_typ_pcompat with (E [ ← Q']); trivial.
destruct (Confluence (U''::Γ) L E H34) as (ZB & a & b & ? & ?). destruct (Confluence Γ U'' C' H33) as (ZA & c & d & ? & ?).
rename H35 into HH35. assert (H35: Γ ⊢ U'' ▹▹ ZA : !s'). eapply typ_reds_relocate. apply HH35. apply H28. clear HH35.
rename H36 into HH36. assert (H36: Γ ⊢ C' ▹▹ ZA : !s2). eapply typ_reds_relocate. apply HH36. apply red_refl_lt in H9; apply H9. clear HH36.
rename H8 into HH8. assert (H8 : U''::Γ ⊢ L ▹▹ ZB : !t'). eapply typ_reds_relocate. apply HH8. apply H29. clear HH8.
rename H13 into HH13. assert (H13 : C'::Γ ⊢ E ▹▹ ZB : !t2). eapply typ_reds_relocate. eapply conv_in_env_reds. apply HH13. eauto.
apply red_refl_lt in H7; apply H7. clear HH13.
clear a b c d.
eapply typ_reds_trans. eapply reds_App. eapply typ_reds_trans. apply H18. constructor. apply H20.  constructor; apply red_refl_lt in H10; apply H10.
constructor; apply red_refl_lt in H9; apply H9. constructor; apply red_refl_lt in H7; apply H7.
eapply typ_reds_trans. eapply reds_App. constructor; apply red_refl_rt in H20; apply H20.  apply H16. apply H36. apply  H13. constructor.
apply typ_pcompat with (ZB [← RQ]). eapply typ_beta. apply H25. apply H28. eapply reds_refl_rt. apply  H35. constructor; apply H28.
trivial. eapply reds_refl_rt. apply H8. apply typ_pcompat with L. trivial. eapply reds_to_conv; apply H8. apply typ_pcompat with C. apply reds_refl_rt in H15; apply H15. eauto.
apply typ_peq_sym. apply reds_to_conv with t2. change !t2 with (!t2[← Q']). eapply reds_subst_gen. apply H13. apply reds_typ_pcompat with C'; eauto.
  (** 2 / 4 **)
destruct H8 as (G0 & G & G' & ? & ? & ? & _ & _ & _ & HH2 & HH1 & HH0). clear x x0. subst. split.
apply reds_typ_pcompat with (D [ ← Q]); trivial.
destruct (Confluence (U''::Γ) K D H31) as (ZB & a & b & ? & ?). destruct (Confluence Γ U'' C H30) as (ZA & c & d & ? & ?).
rename H35 into HH35. assert (H35: Γ ⊢ U'' ▹▹ ZA : !s). eapply typ_reds_relocate. apply HH35. apply H23. clear HH35.
rename H36 into HH36. assert (H36: Γ ⊢ C ▹▹ ZA : !s1). eapply typ_reds_relocate. apply HH36. apply red_refl_lt in H4; apply H4. clear HH36.
rename H8 into HH8. assert (H8 : U''::Γ ⊢ K ▹▹ ZB : !t). eapply typ_reds_relocate. apply HH8. apply H24. clear HH8.
rename H13 into HH13. assert (H13 : C::Γ ⊢ D ▹▹ ZB : !t1). eapply typ_reds_relocate. eapply conv_in_env_reds. apply HH13. eauto.
apply red_refl_lt in H0; apply H0. clear HH13.
clear a b c d.
eapply typ_reds_trans. eapply reds_App. eapply typ_reds_trans. apply H17. constructor. apply H19.  constructor; apply red_refl_lt in H5; apply H5.  constructor; apply red_refl_lt in H4; apply H4.
constructor. apply red_refl_lt in H0; apply H0. eapply typ_reds_trans. eapply reds_App. constructor; apply red_refl_rt in H19; apply H19.  apply H15. apply H36. apply H13. constructor.
apply typ_pcompat with (ZB [← RQ]). eapply typ_beta. apply H21. apply H23. eapply reds_refl_rt. apply H35. constructor. apply H23.
trivial. apply reds_refl_rt in H8; apply H8. apply typ_pcompat with K. trivial. eapply reds_to_conv; apply H8. apply typ_pcompat with C. apply reds_refl_rt in H15; trivial. eauto.
apply typ_peq_sym. apply reds_to_conv with t1. change !t1 with (!t1[← Q]). eapply reds_subst_gen. apply H13.
apply reds_typ_pcompat with C; eauto. apply reds_typ_pcompat with (E [ ← Q']); trivial.
destruct (Confluence (U''::Γ) L E H34) as (ZB & a & b & ? & ?). destruct (Confluence Γ U'' G) as (ZA & c & d & ? & ?).
apply typ_peq_trans with C'; trivial. apply typ_peq_trans with G0. apply reds_to_conv in HH1; eauto. apply reds_to_conv in HH2; eauto.
assert(HEQ1: Γ ⊢ C' ≡' G). apply reds_to_conv in HH1. apply reds_to_conv in HH2. eauto.
rename H35 into HH35. assert (H35: Γ ⊢ U'' ▹▹ ZA : !s'). eapply typ_reds_relocate. apply HH35. apply H28. clear HH35.
rename H36 into HH36. assert (H36: Γ ⊢ G ▹▹ ZA : !s2). eapply typ_reds_relocate. apply HH36. apply reds_refl_rt in HH2; apply HH2. clear HH36.
rename H8 into HH8. assert (H8 : U''::Γ ⊢ L ▹▹ ZB : !t'). eapply typ_reds_relocate. apply HH8. apply H29. clear HH8.
rename H13 into HH13. assert (H13 : G::Γ ⊢ E ▹▹ ZB : !t2). eapply typ_reds_relocate. eapply conv_in_env_reds. apply HH13. eauto. eapply conv_in_env.
apply red_refl_lt in H7; apply H7. eauto. clear HH13.
clear a b c d.
assert (HEQ2: Γ ⊢ Π(C'),E ≡' Π(G),E). apply typ_peq_trans with (Π(G0),E). apply typ_peq_sym.
apply reds_to_conv with u2. eapply reds_Pi. apply HH1.  constructor. eapply conv_in_env. apply red_refl_lt in H7; apply H7. eauto. trivial.
apply reds_to_conv with u2. eapply reds_Pi. apply HH2.  constructor. eapply conv_in_env. apply red_refl_lt in H7; apply H7. eauto. trivial.
eapply typ_reds_trans. eapply reds_App. eapply typ_reds_trans. eapply reds_typ_pcompat with (Π(C'),E). apply H18. trivial. constructor. apply typ_pcompat with (Π(C'),E). apply H20. trivial.
apply reds_typ_pcompat with C'; trivial. constructor; apply red_refl_lt in H10; apply H10.
constructor; apply reds_refl_rt in HH2; apply HH2. eapply conv_in_env_reds. constructor; apply red_refl_lt in H7; apply H7. eauto.
eapply typ_reds_trans. eapply reds_App. apply reds_typ_pcompat with (Π(C'),E); trivial. constructor; apply red_refl_rt in H20; apply H20. apply reds_typ_pcompat with C'; trivial.  apply H16. apply H36. apply  H13. constructor.
apply typ_pcompat with (ZB [← RQ]). eapply typ_beta. apply H25. apply H28. eapply reds_refl_rt. apply  H35. constructor; apply H28.
trivial. eapply reds_refl_rt. apply H8. apply typ_pcompat with L. trivial. eapply reds_to_conv; apply H8. apply typ_pcompat with C. apply reds_refl_rt in H15; apply H15. eauto.
apply typ_peq_sym. apply reds_to_conv with t2. change !t2 with (!t2[← Q']). eapply reds_subst_gen. apply H13. apply reds_typ_pcompat with C'; eauto.
 (** 3 / 4 **)
destruct H8 as (G0 & G & G' & ? & ? & ? & _ & _ & _ & HH2 & HH1 & HH0). subst. clear x x0. destruct H13.
destruct H8 as ( ? & _ & ? & _ ). subst. clear x.  split.
apply reds_typ_pcompat with (D [ ← Q]); trivial.
assert(HEQ1: Γ ⊢ C ≡' G). apply reds_to_conv in HH1. apply reds_to_conv in HH2. eauto.
assert (HEQ2: Γ ⊢ Π(C),D ≡' Π(G),D). apply typ_peq_trans with (Π(G0),D). apply typ_peq_sym.
apply reds_to_conv with u1. eapply reds_Pi. apply HH1.  constructor. eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto. trivial.
apply reds_to_conv with u1. eapply reds_Pi. apply HH2.  constructor. eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto. trivial.
assert (HEQ3: Γ ⊢ C' ≡' G). eauto.
destruct (Confluence (U''::Γ) K D H31) as (ZB & a & b & ? & ?). destruct (Confluence Γ U'' G ) as (ZA & c & d & ? & ?). eauto.
rename H35 into HH35. assert (H35: Γ ⊢ U'' ▹▹ ZA : !s). eapply typ_reds_relocate. apply HH35. apply H23. clear HH35.
rename H36 into HH36. assert (H36: Γ ⊢ G ▹▹ ZA : !s1). eapply typ_reds_relocate. apply HH36. apply reds_refl_rt in HH2; apply HH2. clear HH36.
rename H8 into HH8. assert (H8 : U''::Γ ⊢ K ▹▹ ZB : !t). eapply typ_reds_relocate. apply HH8. apply H24. clear HH8.
rename H13 into HH13. assert (H13 : G::Γ ⊢ D ▹▹ ZB : !t1). eapply typ_reds_relocate.  eapply conv_in_env_reds. apply HH13. eauto. eapply conv_in_env.
apply red_refl_lt in H0;  apply H0. eauto. clear HH13.
clear a b c d.
eapply typ_reds_trans. eapply reds_App. eapply typ_reds_trans. apply reds_typ_pcompat with (Π(C),D); trivial. apply H17. apply reds_typ_pcompat with (Π(C),D); trivial. constructor. apply H19. apply reds_typ_pcompat with C; trivial.
constructor; apply red_refl_lt in H5; apply H5.  constructor; apply reds_refl_rt in HH2; apply HH2.
constructor. eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto. eapply typ_reds_trans. eapply reds_App. apply reds_typ_pcompat with (Π(C),D);trivial.
constructor; apply red_refl_rt in H19; apply H19.  apply reds_typ_pcompat with C; trivial.  apply H15. apply H36. apply H13. constructor.
apply typ_pcompat with (ZB [← RQ]). eapply typ_beta. apply H21. apply H23. eapply reds_refl_rt. apply H35. constructor. apply H23.
trivial. apply reds_refl_rt in H8; apply H8. apply typ_pcompat with K. trivial. eapply reds_to_conv; apply H8. apply typ_pcompat with C. apply reds_refl_rt in H15; trivial. eauto.
apply typ_peq_sym. apply reds_to_conv with t1. change !t1 with (!t1[← Q]). eapply reds_subst_gen. apply H13.
apply reds_typ_pcompat with C; eauto. apply reds_typ_pcompat with (E [ ← Q']); trivial.
destruct (Confluence (U''::Γ) L E H34) as (ZB & a & b & ? & ?). destruct (Confluence Γ U'' C' H33) as (ZA & c & d & ? & ?).
rename H35 into HH35. assert (H35: Γ ⊢ U'' ▹▹ ZA : !s'). eapply typ_reds_relocate. apply HH35. apply H28. clear HH35.
rename H36 into HH36. assert (H36: Γ ⊢ C' ▹▹ ZA : !s2). eapply typ_reds_relocate. apply HH36. apply red_refl_lt in H9; apply H9. clear HH36.
rename H8 into HH8. assert (H8 : U''::Γ ⊢ L ▹▹ ZB : !t'). eapply typ_reds_relocate. apply HH8. apply H29. clear HH8.
rename H13 into HH13. assert (H13 : C'::Γ ⊢ E ▹▹ ZB : !t2). eapply typ_reds_relocate. eapply conv_in_env_reds. apply HH13. eauto.
apply red_refl_lt in H7; apply H7. clear HH13.
clear a b c d.
eapply typ_reds_trans. eapply reds_App. eapply typ_reds_trans. apply H18. constructor. apply H20.  constructor; apply red_refl_lt in H10; apply H10.
constructor; apply red_refl_lt in H9; apply H9. constructor; apply red_refl_lt in H7; apply H7.
eapply typ_reds_trans. eapply reds_App. constructor; apply red_refl_rt in H20; apply H20.  apply H16. apply H36. apply  H13. constructor.
apply typ_pcompat with (ZB [← RQ]). eapply typ_beta. apply H25. apply H28. eapply reds_refl_rt. apply  H35. constructor; apply H28.
trivial. eapply reds_refl_rt. apply H8. apply typ_pcompat with L. trivial. eapply reds_to_conv; apply H8. apply typ_pcompat with C. apply reds_refl_rt in H15; apply H15. eauto.
apply typ_peq_sym. apply reds_to_conv with t2. change !t2 with (!t2[← Q']). eapply reds_subst_gen. apply H13. apply reds_typ_pcompat with C'; eauto.
  (** 4 / 4 **)
destruct H8 as (F0 & F & F' & ? & ? & ? & _ & _ & _  & HH5 & HH4 & HH3). subst. clear x x0.
assert (HEQ1 : Γ ⊢ G ≡' C). apply reds_to_conv in HH1. apply reds_to_conv in HH2. eauto.
assert (HEQ2 : Γ ⊢ F ≡' C'). apply reds_to_conv in HH4. apply reds_to_conv in HH5. eauto.
assert (HEQ3 : Γ ⊢ G ≡' F). apply typ_peq_trans with U''. eauto. eauto.
assert (HEQ4: Γ ⊢ Π(C),D ≡' Π(G),D). apply typ_peq_trans with (Π(G0),D). apply typ_peq_sym.
apply reds_to_conv with u1. eapply reds_Pi. apply HH1.  constructor. eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto. trivial.
apply reds_to_conv with u1. eapply reds_Pi. apply HH2.  constructor. eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto. trivial.
assert (HEQ5: Γ ⊢ Π(C'),E ≡' Π(F),E). apply typ_peq_trans with (Π(F0),E). apply typ_peq_sym.
apply reds_to_conv with u2. eapply reds_Pi. apply HH4.  constructor. eapply conv_in_env. apply red_refl_lt in H7; apply H7. eauto. trivial.
apply reds_to_conv with u2. eapply reds_Pi. apply HH5.  constructor. eapply conv_in_env. apply red_refl_lt in H7; apply H7. eauto. trivial.
split. apply reds_typ_pcompat with (D [ ← Q]); trivial.
destruct (Confluence (U''::Γ) K D H31) as (ZB & a & b & ? & ?). destruct (Confluence Γ U'' G ) as (ZA & c & d & ? & ?). eauto.
rename H35 into HH35. assert (H35: Γ ⊢ U'' ▹▹ ZA : !s). eapply typ_reds_relocate. apply HH35. apply H23. clear HH35.
rename H36 into HH36. assert (H36: Γ ⊢ G ▹▹ ZA : !s1). eapply typ_reds_relocate. apply HH36. apply reds_refl_rt in HH2; apply HH2.  clear HH36.
rename H8 into HH8. assert (H8 : U''::Γ ⊢ K ▹▹ ZB : !t). eapply typ_reds_relocate. apply HH8. apply H24. clear HH8.
rename H13 into HH13. assert (H13 : G::Γ ⊢ D ▹▹ ZB : !t1). eapply typ_reds_relocate. eapply conv_in_env_reds. apply HH13. eauto. eapply conv_in_env.
apply red_refl_lt in H0; apply H0. eauto. clear HH13.
clear a b c d.
eapply typ_reds_trans. eapply reds_App. apply reds_typ_pcompat with (Π(C),D); intuition. eapply typ_reds_trans.  apply H17. constructor. apply H19. apply reds_typ_pcompat with C; intuition.  constructor; apply red_refl_lt in H5; apply H5.
constructor; apply reds_refl_rt in HH2; apply HH2. constructor. eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto. eapply typ_reds_trans. eapply reds_App.
apply reds_typ_pcompat with (Π(C),D).  constructor; apply red_refl_rt in H19; apply H19. intuition.  apply reds_typ_pcompat with C; intuition. apply H15. apply H36. apply H13. constructor.
apply typ_pcompat with (ZB [← RQ]). eapply typ_beta. apply H21. apply H23. eapply reds_refl_rt. apply H35. constructor. apply H23.
trivial. apply reds_refl_rt in H8; apply H8. apply typ_pcompat with K. trivial. eapply reds_to_conv; apply H8. apply typ_pcompat with C. apply reds_refl_rt in H15; trivial. eauto.
apply typ_peq_sym. apply reds_to_conv with t1. change !t1 with (!t1[← Q]). eapply reds_subst_gen. apply H13.
apply reds_typ_pcompat with C; eauto. apply reds_typ_pcompat with (E [ ← Q']); trivial.
destruct (Confluence (U''::Γ) L E H34) as (ZB & a & b & ? & ?). destruct (Confluence Γ U'' F ) as (ZA & c & d & ? & ?). eauto.
rename H35 into HH35. assert (H35: Γ ⊢ U'' ▹▹ ZA : !s'). eapply typ_reds_relocate. apply HH35. apply H28. clear HH35.
rename H36 into HH36. assert (H36: Γ ⊢ F ▹▹ ZA : !s2). eapply typ_reds_relocate. apply HH36. apply reds_refl_rt in HH5; apply HH5.  clear HH36.
rename H8 into HH8. assert (H8 : U''::Γ ⊢ L ▹▹ ZB : !t'). eapply typ_reds_relocate. apply HH8. apply H29. clear HH8.
rename H13 into HH13. assert (H13 : F::Γ ⊢ E ▹▹ ZB : !t2). eapply typ_reds_relocate. eapply conv_in_env_reds. apply HH13. eauto. eapply conv_in_env.
apply red_refl_lt in H7; apply H7. eauto. clear HH13.
clear a b c d.
eapply typ_reds_trans. eapply reds_App. apply reds_typ_pcompat with (Π(C'),E). eapply typ_reds_trans. apply H18. constructor. apply H20. intuition. apply reds_typ_pcompat with C'; intuition.  constructor; apply red_refl_lt in H10; apply H10.
constructor; apply reds_refl_rt in HH5; apply HH5. eapply conv_in_env_reds. constructor; apply red_refl_lt in H7; apply H7. eauto.
eapply typ_reds_trans. eapply reds_App. apply reds_typ_pcompat with (Π(C'),E). constructor; apply red_refl_rt in H20; apply H20. intuition. apply reds_typ_pcompat with C'; intuition.  apply H16. apply H36. apply  H13. constructor.
apply typ_pcompat with (ZB [← RQ]). eapply typ_beta. apply H25. apply H28. eapply reds_refl_rt. apply  H35. constructor; apply H28.
trivial. eapply reds_refl_rt. apply H8. apply typ_pcompat with L. trivial. eapply reds_to_conv; apply H8. apply typ_pcompat with C. apply reds_refl_rt in H15; apply H15. eauto.
apply typ_peq_sym. apply reds_to_conv with t2. change !t2 with (!t2[← Q']). eapply reds_subst_gen. apply H13. apply reds_typ_pcompat with C'; eauto.
  (** impossible cases **)
destruct H19 as (z & ? & ?). apply red_refl_rt in H19. apply pgen_sort in H19 as ( ? & ? & ? & ?).
destruct H22. discriminate. apply peq_not_Pi_sort in H22; elim H22.

destruct H19 as (U & V & ? & ?). apply red_refl_rt in H19. apply pgen_pi in H19 as ( U' & V' & s & t & u & h).
decompose [and] h; clear h. destruct H25. discriminate. apply peq_not_Pi_sort in H24; elim H24.
(**)
destruct N; simpl in H; try discriminate. injection H; intros; subst; clear H.
apply pgen_pi in H0. destruct H0 as (M1' & M2' & s1 & t1 & u1 & h). decompose [and] h; clear h.
apply pgen_pi in H1. destruct H1 as (N1' & N2' & s2 & t2 & u2 & h). decompose [and] h; clear h.
apply red_refl_lt in H4. apply red_refl_lt in H8.
destruct (IHM1 N1 Γ !s1 !s2 H3 H4 H8) as (R1 &  ? & ?).
assert (Γ ⊢ M1 ≡' N1). apply typ_peq_trans with R1. apply reds_to_conv in H10; trivial. apply reds_to_conv in H12; intuition.
apply red_refl_lt in H0.
destruct (IHM2 N2 (M1::Γ) !t1 !t2 H2 H0 ) as (R2 & ? & ?).
eapply conv_in_env. apply red_refl_lt in H6; apply H6.
eauto. exists (Pi R1 R2); split.
destruct H7. subst.  eapply reds_Pi. apply H10. apply H14. trivial.
apply reds_typ_pcompat with !u1. eapply reds_Pi.  apply H10. apply H14. trivial. intuition.
destruct H11. subst.  eapply reds_Pi. apply H12. eapply conv_in_env_reds. apply H15. eauto. trivial.
apply reds_typ_pcompat with !u2. eapply reds_Pi. apply H12. eapply conv_in_env_reds. apply H15. eauto. trivial. intuition.
(**)
destruct N; simpl in H; try discriminate. injection H; intros; subst; clear H.
apply pgen_la in H0. destruct H0 as (M1' & M2' & D & s1 & t1 & u1 & h). decompose [and] h; clear h.
apply pgen_la in H1. destruct H1 as (N1' & N2' & D2 & s2 & t2 & u2 & h). decompose [and] h; clear h.
apply red_refl_lt in H4. apply red_refl_lt in H9.
destruct (IHM1 N1 Γ !s1 !s2 H3 H4 H9) as (R1 & ? & ? ).
assert (Γ ⊢ M1 ≡' N1). apply typ_peq_trans with R1. apply reds_to_conv in H12; trivial. apply reds_to_conv in H14; intuition.
destruct (IHM2 N2 (M1::Γ) D D2 H2) as (R2 & ? & ? ); trivial.
eapply conv_in_env. apply red_refl_lt in H0; apply H0. eauto.
eapply conv_in_env. apply red_refl_lt in H7; apply H7. eauto.
exists (La R1 R2); split.
apply reds_typ_pcompat with (Π (M1), D); trivial. eapply reds_La.  apply H12. trivial. apply H5. apply H.
apply reds_typ_pcompat with (Π (N1), D2); trivial. eapply reds_La. apply H14. eapply conv_in_env_reds.  apply H17. eauto.
apply H10. apply H1.
Qed.


(** Next step: if there is a path for any term, there is path for types, so two
  version of a same "stripped" types are equivalent in PTS_{atr}.*)
Lemma ErasedTypeConversion : forall A B Γ s t, strip A = strip B -> Γ ⊢ A ▹ A : !s -> Γ ⊢ B ▹ B : !t ->
  Γ ⊢ A ≡' B.
intros.
destruct (ErasedTermConfluence A B Γ !s !t H H0 H1) as ( P & ?&  ?).
apply typ_peq_trans with P. apply reds_to_conv in H2; trivial. apply reds_to_conv in H3; intuition.
Qed.

(** And if it's true for types, its true for list of types, so for context.*)
Lemma L43_ : forall Γ Γ', strip_env Γ = strip_env Γ' -> wf Γ -> wf Γ' -> env_conv Γ Γ'.
induction Γ; intros. destruct Γ'; simpl in H.
intuition. discriminate. destruct Γ'; simpl in *. discriminate.
injection H; intros; subst; clear H. eapply c_trans with (a::Γ').
apply env_conv_cons. inversion H0; subst; clear H0. econstructor. apply red_refl_lt in H4; apply H4.
inversion H1; inversion H0; subst; clear H0 H1. apply wf_from_typ in H4. apply wf_from_typ in H7. intuition.
apply env_conv_cons.  inversion H1; inversion H0; subst; clear H0 H1.
eapply ErasedTypeConversion. trivial. eapply conv_in_env.
apply red_refl_lt in H7; apply H7.
apply IHΓ. trivial. apply wf_from_typ in H7; trivial.
apply wf_from_typ in H4; trivial. apply red_refl_lt in H4; apply H4.
inversion H1; inversion H0; subst; clear H0 H1.
apply wf_from_typ in H4. apply wf_from_typ in H7. intuition.
Qed.

(** Now that we know that two versions of a "stripped" context are equivalent,
we can chose to use both version to build our judgment. This well be usefull to
glue together the intermediate steps of the annotations process.*)
Lemma ErasedContextSwitch : (forall Γ M N T, Γ ⊢ M ▹ N : T -> forall  Γ', wf Γ' -> strip_env  Γ = strip_env  Γ' -> Γ' ⊢ M ▹ N : T) /\
  (forall Γ M N T, Γ ⊢ M ▹▹ N : T -> forall  Γ', wf Γ' -> strip_env  Γ = strip_env  Γ' -> Γ' ⊢ M ▹▹ N : T) /\
  (forall Γ, Γ ⊣ -> True).
apply typ_induc; simpl; intros; trivial.
(**)
apply conv_in_env with  Γ. intuition. apply L43_; trivial.
(**)
intuition.
(**)
apply typ_pi with s1 s2; intuition. eapply H0. econstructor. eapply H.
trivial. trivial. simpl; rewrite H2; trivial.
(**)
apply typ_la with s1 s2 s3; intuition. eapply H0. econstructor. eapply H.
trivial. trivial. simpl; rewrite H3; trivial. eapply H1. econstructor. eapply H.
trivial. trivial. simpl; rewrite H3; trivial.
(**)
eapply typ_app.  apply r.  eapply H; eauto.  eapply H0; eauto.  simpl. rewrite H4; intuition.
eapply H1; eauto. eapply H2; eauto.
(**)
eapply typ_beta. apply r. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
eapply H2; eauto. eapply H3; eauto. simpl; rewrite H7; trivial. eapply H4; eauto.
simpl; rewrite H7; trivial. eapply H5; eauto.
(**)
eauto.
(**)
eauto.
(* reds *)
eauto. eauto.
Qed.

(** Some property of the stripping process and reduction .*)
Lemma L33 : forall M N', URM.Beta (strip M) N' ->exists N, strip N = N' /\ Beta M N.
induction M; intros; simpl in *.
inversion H. inversion H.
inversion H; subst; clear H. destruct M1; simpl in *; try discriminate.
injection H1; intros; subst; clear H1.
exists ( M1_2 [ ← M4]); split. rewrite strip_subst. trivial. eauto.
destruct (IHM1 M' H3) as (n & ? & ?). exists (App n M2 M3 M4); split. simpl. subst. trivial.
intuition. destruct (IHM4 N'0 H3) as (n & ? & ?). exists (App M1 M2 M3 n); split. simpl. subst. trivial.
intuition. inversion H; subst; clear H.
destruct (IHM2 B' H3) as (n & ? & ?). exists (Pi M1 n); split. simpl. subst. trivial.
intuition. destruct (IHM1 A' H3) as (n & ? & ?). exists (Pi n M2); split. simpl. subst. trivial.
intuition.  inversion H; subst; clear H.
destruct (IHM2 M' H3) as (n & ? & ?). exists (La M1 n); split. simpl. subst. trivial.
intuition. destruct (IHM1 A' H3) as (n & ? & ?). exists (La n M2); split. simpl. subst. trivial.
intuition.
Qed.

Lemma L33' : forall M N', URM.Betas (strip M) N' ->exists N, strip N = N' /\ Betas M N.
intros. remember (strip M) as MM. revert M HeqMM. induction H; intros; subst.
exists M0; intuition. apply L33 in H as (N0 & ? & ?).
exists N0; intuition. destruct (IHBetas1 M0 ) as (N0 & ? & ?); trivial.
destruct (IHBetas2 N0) as (NN & ?& ?). intuition.
exists NN; intuition. eauto.
Qed.


End glue_mod.