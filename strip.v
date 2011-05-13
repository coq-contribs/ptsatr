(** * Stripping functions
In this file, we describe how to get rid of the annotations
introduced in PTSATR, to translate terms from PTSATR to PTS or PTSe.*)
Require Import base.
Require Import ut_term.
Require Import ut_red.
Require Import ut_env.
Require Import term.
Require Import env.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import List.

Module strip_mod (X:term_sig) (TM:ut_term_mod X) (T'M : term_mod X) (EM: ut_env_mod X TM) (E'M: env_mod X T'M).
 Import X TM T'M.

Open Scope Typ_scope.
(** Stripping function for terms and contexts.*)
Fixpoint strip (T : T'M.Term ) : TM.Term := match T with
 | Pi A B => TM.Pi (strip A) (strip B)
 | La A M => TM.La (strip A) (strip M)
 | App M A B N => TM.App (strip M) (strip N)
 | !s => TM.Sort s
 | #x => TM.Var x
end.

Fixpoint strip_env (Γ: E'M.Env) : EM.Env := match Γ with
 | nil   => nil
 | A::Γ' => (strip A)::(strip_env Γ')
end.

(** Stripping doesn't not mess with lift or subst .*)
Lemma strip_lift : forall M n m, strip (M ↑ n # m) = ((strip M) ↑ n # m)%UT.
induction M; intros; simpl in *.
destruct le_gt_dec; simpl; trivial.
trivial.
rewrite IHM1, IHM4; trivial.
rewrite IHM1, IHM2; trivial.
rewrite IHM1, IHM2; trivial.
Qed.

Lemma strip_subst : forall M n N, strip (M [n ← N]) = ((strip M) [ n ← strip N])%UT.
induction M; intros; simpl in *.
destruct lt_eq_lt_dec as [ [] | ]; simpl; trivial.
rewrite strip_lift. trivial.
trivial.
rewrite IHM1, IHM4; trivial.
rewrite IHM1, IHM2; trivial.
rewrite IHM1, IHM2; trivial.
Qed.

End strip_mod.
