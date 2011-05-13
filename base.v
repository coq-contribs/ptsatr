(** * Abstract Parameters of PTS

a PTS depends on two sets that control typing of 
sorts and Π-types, and two other sets that define
what is a sort and what is a variable. *)

(** ** Sorts and Variables 

Sorts can be anything we want: *)
Module Type term_sig.
  Parameter Sorts : Set.
End term_sig.

Module Type pts_sig (X:term_sig).
  Import X.
(** [Ax] is used to type [Sorts]. *)
  Parameter Ax : Sorts -> Sorts -> Prop.
(** [Rel] is used to type Π-types. *)
  Parameter Rel : Sorts -> Sorts -> Sorts -> Prop.
End pts_sig.

(** To deal with variable binding, we use de Bruijn indexes: *)
Definition Vars := nat.
