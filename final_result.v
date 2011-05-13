(** * Final Result : PTS <-> PTSe 
Here we use PTS_{atr} as an intermediate system to prove that any judgement in PTS
can be lifted in PTSe, which means that we can build a valid equality judgement
from a Beta conversion.

Then we will use this equivalence to prove that PTSe enjoys the Subject Reduction
property.
*)

Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.


Require Import base.
Require Import ut_term.
Require Import ut_red.
Require Import ut_env.
Require Import ut_red ut_typ.
Require Import ut_sr ut_typ_eq.
Require Import term.
Require Import red env.
Require Import typ_annot.
Require Import glue.
Require Import List.
Require Import strip.

Module final_mod  (X:term_sig) (Y:pts_sig X) 
  (TM:term_mod X) (EM: env_mod X TM) (RM: red_mod X TM)
  (UTM:ut_term_mod X) (UEM: ut_env_mod X UTM) (URM: ut_red_mod X UTM)
  (PTS : ut_sr_mod X Y UTM UEM URM) (PTSe : ut_typ_eq_mod X Y UTM UEM URM PTS)
  (PTS_ATR: glue_mod X Y TM EM RM UTM UEM URM).
 Import X Y UTM UEM URM TM EM RM PTS PTSe PTS_ATR.

Open Scope Typ_scope.

(** Now that we know how to glue types and contexts together, we can 
annotate a PTS judgement into a PTS_{atr} one.*)
Lemma FromPTS_to_PTSATR : (forall Γ  M A , PTS.typ Γ M A -> exists Γ', exists M', exists A', strip_env Γ' = Γ /\ 
  strip M' = M /\ strip A' = A /\ Γ' ⊢ M' ▹ M' : A') /\
        (forall Γ , PTS.wf Γ -> exists Γ', strip_env Γ' = Γ /\ wf Γ').
apply PTS.typ_induc; intros.
destruct H as (Γ' & ? & ?). exists Γ'; exists !s; exists !t; intuition.
(**)
destruct H as (ΓΓ & ? & ?). assert (exists AA, AA ↓ v ⊂ ΓΓ /\ A = strip AA).
clear w H0. revert ΓΓ A v H i. induction Γ; intros. destruct i as ( a & ? &?).
inversion H1. destruct ΓΓ; simpl in H. discriminate. injection H; intros; subst; clear H.
destruct i as (a &? & ?). inversion H0; subst; clear H0. exists (lift_rec 1 0 t).
split. exists t. intuition. rewrite strip_lift; trivial. 
destruct (IHΓ ΓΓ (UTM.lift_rec (S n) 0 a) n) as (B & ?& ?). trivial.
exists a; intuition. exists (lift_rec 1 0 B). split. destruct H as (b & ?& ?).
exists b. subst. rewrite lift_lift; intuition. rewrite strip_lift. rewrite <- H0.
rewrite UTM.lift_lift. trivial.
destruct H1 as (B &? & ?). exists ΓΓ; exists #v; exists B; simpl; intuition.
(**)
destruct H as (Γa & A' & ? & ? & ? & ? & ?). destruct x; simpl in H2; try discriminate.
injection H2; intros; subst; clear H2.
destruct H0 as (Γb & B' & ? & ? & ? & ? & ?). destruct x; simpl in H1; try discriminate.
injection H1; intros; subst; clear H1.
exists Γa ; exists (Pi A' B'); exists !u; simpl; intuition. econstructor.
apply r. trivial. eapply ErasedContextSwitch. apply H2. econstructor. eapply H3. simpl; trivial.
(**)
destruct H as (Γa & Ma & ? & ? & ?& ? & ?). destruct x; simpl in H3; try discriminate.
injection H3; intros; subst; clear H3. destruct H0 as (Γb & Mb & ? & ? & ? & ? & ?).
destruct x; simpl in H2; try discriminate. injection H2; intros; subst; clear H2.
destruct H1 as (Γm & M' & B' & ? & ?& ? &?). destruct Γb; simpl in H. discriminate.
injection H; intros; subst; clear H. destruct Γm; simpl in H0. discriminate.
injection  H0; intros; subst; clear H0.
exists Γa; exists (La Ma M'); exists (Pi Ma Mb); simpl; intuition. econstructor.
apply r. trivial. eapply ErasedContextSwitch. apply H3. econstructor. apply H4. simpl. rewrite H6. rewrite H7. trivial.
destruct (typ_wf (t3 :: Γm)  M' M' B' H5). destruct H0; subst. simpl in H2; destruct Mb; try discriminate.
simpl in H2. injection H2; intros; subst; clear H2. eapply ErasedContextSwitch. apply H5.  econstructor. apply H4.
simpl. rewrite H1; rewrite H; trivial. destruct H0 as ( x & ?).
eapply ErasedContextSwitch. apply typ_pcompat with B'. apply H5. eapply ErasedTypeConversion. trivial. apply H0. 
eapply ErasedContextSwitch. apply H3. apply wf_from_typ in H0; trivial. simpl. rewrite H7; rewrite H1; rewrite H6; rewrite H; trivial.
econstructor. apply H4. simpl. rewrite H1; rewrite H; trivial.
(**)
destruct H as (Γm & Mm & Tm & ? & ? & ? &?). destruct Tm; simpl in *; try discriminate. 
injection H2; intros; subst; clear H2. destruct H0 as (Γn & Mn & Tn &? & ? & ?& ?).
exists Γm; exists (App Mm Tm1 Tm2 Mn); exists (Tm2  [ ← Mn]); intuition.
subst. simpl. trivial. rewrite strip_subst. subst. trivial.
assert (exists u, Γm ⊢ Π (Tm1),Tm2 ▹ Π(Tm1),Tm2 : !u). apply typ_wf in H3.
destruct H3. destruct H3 ; discriminate. trivial. destruct H4 as (u& ?).
apply pgen_pi in H4 as (Tm1' & Tm2' & s1 & s2 & s3 & h); decompose [and] h; clear h.
injection H7; intros; subst; clear H7.
econstructor. apply H4. apply H6. trivial. trivial. apply typ_pcompat with Tn. eapply ErasedContextSwitch.
apply H2. apply wf_from_typ in H6; trivial. trivial. apply typ_wf in H2. destruct H2 as [ [ s ?] | [s ?] ].
subst. destruct Tm1'; simpl in H1; try discriminate. injection H1; intros; subst; clear H1.
econstructor. apply H6. eapply ErasedTypeConversion. trivial. eapply ErasedContextSwitch. apply H0. apply wf_from_typ in H6; trivial.
trivial. apply H6.
(**)
destruct H as (Γ' & M' & A' & ? & ? & ? & ?). destruct H0 as (Γ2 & B' & Tb & ? & ?& ?& ?).
destruct Tb; simpl in H5; try discriminate. injection H5; intros; subst; clear H5.
destruct (typ_wf Γ' M' M' A' H3). destruct H as (a & ?). subst; simpl in b.
apply URM.conv_to_sort in b.
apply L33' in b. destruct b as ( n & ? & ?). destruct n; simpl in H; try discriminate.
injection H; intros; subst; clear H.
exists Γ'; exists M' ; exists B'; intuition. apply typ_pcompat with !a.
trivial. apply typ_peq_sym. apply reds_to_conv with s.
apply SR_trans' with B'; trivial. eapply ErasedContextSwitch. apply H6. apply wf_from_typ in H3; trivial. trivial.
destruct H as (sA' & ?). apply URM.Betac_confl in b as (C & ?& ?).
apply L33' in H1 as (C0 & ? & ?). apply L33' in H2 as (C1 & ? & ?).
exists Γ'; exists M'; exists B'; intuition. eapply typ_pcompat with A'.
trivial. assert (Γ' ⊢ A' ▹▹ C0 : !sA').   apply SR_trans' with A'. trivial. trivial.
assert (Γ' ⊢ B' ▹▹ C1 : !s).   apply SR_trans' with B'. trivial. eapply ErasedContextSwitch.
apply H6. apply wf_from_typ in H3; trivial. trivial. apply typ_peq_trans with C0.
apply reds_to_conv with sA'; trivial.  apply typ_peq_trans with C1.
eapply ErasedTypeConversion. rewrite H1. rewrite H2. trivial. apply reds_refl_rt in H7; apply H7. 
apply reds_refl_rt in H8; apply H8.  apply typ_peq_sym.
apply reds_to_conv with s; trivial.
(* wf *)
exists nil; simpl; intuition.
(**)
destruct H as (Γ' & M' & A' & ? & ? & ? & ?).
destruct A'; simpl in H1; try discriminate. injection H1; intros; subst; clear H1.
exists (M'::Γ'); simpl; intuition. econstructor. apply H2.
Qed.





(* begin hide *)
Lemma strip_var_ : forall Γ x A, A↓ x ∈ Γ -> ((strip A)↓ x ∈ (strip_env Γ))%UT.
induction Γ; intros.
inversion H.
inversion H; intros; subst.
simpl; constructor.
simpl. intuition.
Qed.

Lemma strip_var : forall Γ x A, A ↓ x ⊂ Γ -> ((strip A) ↓ x ⊂ (strip_env Γ))%UT.
intros. destruct H as (a  & ? & ?).
apply strip_var_ in H0. exists (strip a); intuition.
rewrite <- strip_lift. rewrite H. trivial.
Qed.
(* end hide *)


(** Easy part of the translation: by stripping the application of their
annotations, we prove that:
  - a valid PTS_{atr} judgement can be stripped to a valide PTS judgement
  - a valid PTS_{atr} judgement can be stripped to a valide PTSe judgement
*)
Lemma FromPTSATR_to_PTS : (forall Γ M N T, Γ ⊢ M ▹ N : T -> (strip_env Γ) ⊢  (strip M) : (strip T) /\
   (strip_env Γ) ⊢ (strip N) : (strip T) /\ (strip M) ≡ (strip N)) /\
(forall Γ M N T, Γ ⊢ M ▹▹ N : T -> (strip_env Γ) ⊢  (strip M) : (strip T) /\
   (strip_env Γ) ⊢ (strip N) : (strip T) /\ (strip M) ≡ (strip N)) /\
 (forall Γ, Γ ⊣ -> ((strip_env Γ) ⊣)%UT).
apply typ_induc; intros; simpl in *.
split. apply strip_var in i. intuition.
split. apply strip_var in i. intuition.
trivial.
(**)
intuition.
(**)
destruct H as (? & ?& ?), H0 as (? & ? & ?).
split. apply PTS.cPi with s1 s2; trivial.
split.  apply PTS.cPi with s1 s2; trivial.
apply Betac_confl in H2 as (Z & ?& ?). apply Betas_env_sound_up with (Z::(strip_env Γ)).
apply Betas_env_sound with ((strip A)::(strip_env Γ)). trivial. apply Betas_env_hd; trivial.
eauto. apply Betas_env_hd; trivial. intuition.
(**)
destruct H as (? & ?& ?), H0 as (? & ?& ?), H1 as (? & ? & ?).
split. apply PTS.cLa with s1 s2 s3; trivial. split. apply PTS.Cnv with (Π(strip A'),strip B)%UT s3.
intuition. apply PTS.cLa with s1 s2 s3; trivial. apply Betac_confl in H3 as (Z & ?& ?). apply Betas_env_sound_up with (Z::(strip_env Γ)).
apply Betas_env_sound with ((strip A)::(strip_env Γ)). trivial. apply Betas_env_hd; trivial.
eauto. apply Betas_env_hd; trivial. apply Betac_confl in H3 as (Z & ?& ?). apply Betas_env_sound_up with (Z::(strip_env Γ)).
apply Betas_env_sound with ((strip A)::(strip_env Γ)). trivial. apply Betas_env_hd; trivial.
eauto. apply Betas_env_hd; trivial. apply PTS.cPi with s1 s2; trivial. intuition.
(**)
destruct H as (? & ?& ?), H0 as (? & ?& ?), H1 as (? & ? & ?), H2 as (? & ?& ?).
split. rewrite strip_subst. apply PTS.cApp with (strip A); trivial. split. rewrite strip_subst.
apply PTS.Cnv with ((strip B)[← strip N'])%UT s2. intuition. apply PTS.cApp with (strip A); trivial.
change (!s2)%UT with (!s2[← strip N])%UT. eapply PTS.substitution. apply H0. apply H2. constructor. eauto.
intuition.
(**)
destruct H as (? & ?& ?), H0 as (? & ?& ?), H1 as (? & ? & ?), H2 as (? & ?& ?), H3 as (? & ?& ?),  
  H4 as (? & ?& ?), H5 as (? & ?& ?).
split. rewrite strip_subst. apply PTS.cApp with (strip A). apply PTS.cLa with s1 s2 s3; trivial. trivial.
split. rewrite 2! strip_subst. apply PTS.Cnv with ((strip B)[← strip N'])%UT s2. intuition. eapply PTS.substitution.
apply H16. apply H18. constructor. eauto. change (!s2)%UT with (!s2[← strip N])%UT. eapply PTS.substitution. apply H3. apply H5. constructor. eauto.
rewrite strip_subst. apply Betac_trans with ((strip M)[← strip N])%UT. intuition.
apply Betac_trans with ((strip M)[← strip N'])%UT. intuition. intuition.
(**)
destruct H as (? & ? & ?), H0 as (? & ?& ?).
split. apply PTS.Cnv with (strip A) s; trivial. split. apply PTS.Cnv with (strip A) s; trivial. trivial.
(**)
destruct H as (? & ? & ?), H0 as (? & ?& ?).
split. apply PTS.Cnv with (strip B) s; intuition. split. apply PTS.Cnv with (strip B) s; intuition. trivial.
(* reds *) 
eauto.
(**)
destruct H as (? & ? & ?), H0 as ( ? & ?& ?); eauto.
(* wf *)
trivial.
(**)
destruct H as (? & ?& ?). eauto.
Qed.


Lemma FromPTSATR_to_PTSe : (forall Γ M N T, Γ ⊢ M ▹ N : T -> (strip_env Γ) ⊢e  (strip M) = (strip N)  : (strip T)) /\
 (forall Γ M N T, Γ ⊢ M ▹▹ N : T -> (strip_env Γ) ⊢e  (strip M) = (strip N)  : (strip T)) /\
 (forall Γ, (PTS_ATR.wf Γ) -> ((strip_env Γ) ⊣e)%UT).
apply PTS_ATR.typ_induc; intros; simpl in *.
(**)
apply strip_var in i. intuition.
(**)
intuition.
(**)
apply cPi_eq with s1 s2; trivial.
(**)
apply cLa_eq with s1 s2 s3; trivial. change (strip A::strip_env Γ) with( nil++strip A::strip_env Γ).
eapply PTSe.conv_in_env. apply left_reflexivity in H0. apply H0. simpl; reflexivity. constructor.
apply left_reflexivity in H. apply H. apply left_reflexivity   with (strip A'); trivial.
(**)
rewrite strip_subst. apply cApp_eq with (strip A). trivial. trivial.
(**)
rewrite 2! strip_subst. apply cTrans with ((strip M)[← strip N])%UT. apply cBeta with s1 s2 s3; trivial.
apply left_reflexivity with (strip A'); trivial. apply left_reflexivity with (strip B'); trivial.
apply left_reflexivity with (strip M'); trivial. apply left_reflexivity with (strip N'); trivial.
apply cTrans with ((strip M')[← strip N])%UT. eapply substitution. apply H4. apply left_reflexivity in H5; apply H5.
constructor. eapply substitution2. apply right_reflexivity in H4; apply H4. apply H5. apply left_reflexivity with (strip N'); trivial.
constructor.
(**)
apply Cnv_eq with (strip A) s; trivial.
(**)
apply Cnv_eq with (strip B) s; intuition.
(* reds *)
eauto.
(**) 
eauto.
(* wf *)
trivial.
econstructor. apply left_reflexivity in H. apply H.
Qed.

Lemma FromPTSATR_to_PTSe_trans : forall Γ M N T, Γ ⊢ M ▹▹ N : T -> (strip_env Γ) ⊢e  (strip M) = (strip N)  : (strip T).
induction 1. apply FromPTSATR_to_PTSe in H. trivial.
eauto.
Qed.

(** With the previous result, we can complete the following chart:
 - ut_typ_eq.v : PTSe  -> PTS
 -             : PTS   -> PTS_{atr}
 -             : PTS_{atr} -> PTS
 -             : PTS_{atr} -> PTSe
So PTSe -> PTS -> PTS_{atr} -> PTSe which prove that PTSe <-> PTS.*)
Lemma PTS_equiv_PTSe : (forall Γ M T, Γ ⊢ M : T <-> Γ ⊢e M : T) /\
  (forall Γ M N T, Γ ⊢e M = N : T <-> Γ ⊢ M : T /\ Γ ⊢ N : T /\ M ≡ N).
split. intros. split; intros.
apply FromPTS_to_PTSATR in H. destruct H as (Γ' & M' & T'& ? & ? & ? & ?).
apply FromPTSATR_to_PTSe in H2. rewrite H in H2. rewrite H0 in H2. rewrite H1 in H2. apply left_reflexivity with M; trivial.
apply FromPTSe_to_PTS in H. trivial.
(**)
intros. split; intros.
apply FromPTSe_to_PTS in H. trivial.
destruct H as ( ? & ?& ?).  apply Betac_confl in H1 as (P & ?& ?). apply cTrans with P.
apply FromPTS_to_PTSATR in H as (Γ1 & M1 & T1 & ? & ? & ?& ?).  destruct (L33' M1 P) as (P1 & ? & ?).
rewrite H3; trivial. subst. apply FromPTSATR_to_PTSe_trans. apply SR_trans' with M1; trivial.
apply cSym.
apply FromPTS_to_PTSATR in H0 as (Γ1 & N1 & T1 & ? & ? & ?& ?).  destruct (L33' N1 P) as (P1 & ? & ?).
rewrite H3; trivial. subst. apply FromPTSATR_to_PTSe_trans. apply SR_trans' with N1; trivial.
Qed.



Print Assumptions PTS_equiv_PTSe.

(* Now, we just have to import the Subject Reduction property from PTS
to PTSe. *)
Lemma PTSe_SR : forall Γ M N T, Γ ⊢e M : T -> (M → N)%UT -> Γ ⊢e M = N : T.
intros. 
apply FromPTSe_to_PTS in H.
apply FromPTS_to_PTSATR in  H as (Γ' & M' & T' & ? & ? & ? & ?).
subst. apply L33 in H0 as (N' & ? & ?). subst. 
apply FromPTSATR_to_PTSe_trans. eapply SR_trans'.
intuition. apply H3.
Qed.

Lemma PTSe_SR_trans : forall Γ M N T, Γ ⊢e M : T -> (M →→ N)%UT -> Γ ⊢e M = N : T.
intros.
induction H0.
intuition.
apply PTSe_SR; trivial.
assert (Γ ⊢e M = N : T). intuition.
apply cTrans with N. trivial.
apply IHBetas2. apply right_reflexivity in H0; trivial.
Qed.

End final_mod.



Module Type Theory (X:term_sig) (Y:pts_sig X) .
Module PTSATR.
  Include term_mod X.
  Include env_mod X.
  Include red_mod X.
End PTSATR.

Module PTS.
  Include ut_term_mod X.
  Include ut_env_mod X.
  Include ut_red_mod X.
  Include ut_sr_mod X Y.
End PTS.


Module PTSe.
 Include ut_typ_eq_mod X Y PTS PTS PTS PTS.
End PTSe.

Include glue_mod X Y PTSATR PTSATR PTSATR PTS PTS PTS.
Include final_mod X Y PTSATR PTSATR PTSATR PTS PTS PTS PTS PTSe.

Export PTSATR PTS PTSe.
End Theory.


