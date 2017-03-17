(**************************************************************************)
(*              Coherence of first-order Heyting arithmetic               *)
(*                                                                        *)
(*                         © 2011 Stéphane Glondu                         *)
(*                         © 2013 Pierre Letouzey                         *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*   it under the terms of the CeCILL free software license, version 2.   *)
(**************************************************************************)

Require Import List.
Require Import Arith.
Require Import Omega.

(* Terms *)

Inductive term :=
  | Tvar : nat -> term
  | Tzero : term
  | Tsucc : term -> term
  | Tplus : term -> term -> term
  | Tmult : term -> term -> term
.

(* Add n to all variables of t >= k *)

Fixpoint tlift n t k :=
  match t with
    | Tvar i => Tvar (if le_gt_dec k i then n+i else i)
    | Tzero => Tzero
    | Tsucc u => Tsucc (tlift n u k)
    | Tplus u v => Tplus (tlift n u k) (tlift n v k)
    | Tmult u v => Tmult (tlift n u k) (tlift n v k)
  end
.

Lemma tlift_1 : forall t n n' k k', k <= k' -> k' <= k + n ->
  tlift n' (tlift n t k) k' = tlift (n' + n) t k.
Proof.
  induction t; intros; simpl; f_equal; auto.
  repeat (destruct le_gt_dec); omega.
Qed.

Lemma tlift_2 : forall t n n' k k', k' <= k ->
  tlift n' (tlift n t k) k' = tlift n (tlift n' t k') (n' + k).
Proof.
  induction t; intros; simpl; f_equal; auto.
  repeat (destruct le_gt_dec); omega.
Qed.

(* Replace variable x by (tlift x t' 0) in t *)

Fixpoint tsubst x t' t :=
  match t with
    | Tvar i =>
      match nat_compare x i with
        | Eq => tlift x t' 0
        | Lt => Tvar (pred i)
        | Gt => Tvar i
      end
    | Tzero => Tzero
    | Tsucc u => Tsucc (tsubst x t' u)
    | Tplus u v => Tplus (tsubst x t' u) (tsubst x t' v)
    | Tmult u v => Tmult (tsubst x t' u) (tsubst x t' v)
  end
.

(* A version of omega also handling false non-arithmetical goals *)
Ltac omega' := omega || exfalso; omega.

Ltac break := match goal with
 | |- context [ le_gt_dec _ _ ] => destruct le_gt_dec
 | |- context [ nat_compare ?x ?y ] => destruct (nat_compare_spec x y)
end.


Lemma tsubst_1 : forall t x t' n k, k <= x -> x <= k + n ->
  tsubst x t' (tlift (S n) t k) = tlift n t k.
Proof.
  induction t; intros; simpl; f_equal; auto.
  repeat break; subst; simpl; f_equal; omega'.
Qed.

Lemma tsubst_2 : forall t x t' n k, k <= x ->
  tlift n (tsubst x t' t) k = tsubst (n + x) t' (tlift n t k).
Proof.
  induction t; intros; simpl; f_equal; auto.
  repeat (break; simpl; rewrite ?tlift_1); f_equal; try omega'.
Qed.

Lemma tsubst_3 : forall t x t' n k,
  tlift n (tsubst x t' t) (x + k) =
  tsubst x (tlift n t' k) (tlift n t (S (x + k))).
Proof.
  induction t; intros; simpl; f_equal; auto.
  destruct n; repeat (break; simpl in *; try reflexivity; try omega').
  subst; rewrite <- tlift_2; f_equal; omega.
  f_equal; omega.
  rewrite <- tlift_2; f_equal; omega.
Qed.

Lemma tsubst_4 : forall t x t' y u',
  tsubst (x + y) u' (tsubst x t' t) =
  tsubst x (tsubst y u' t') (tsubst (S (x + y)) u' t).
Proof.
  induction t; intros; simpl; try (f_equal; auto; fail).
  destruct n; repeat (break; simpl in *; try reflexivity; try omega').
  rewrite tsubst_2; reflexivity || omega.
  rewrite tsubst_2; reflexivity || omega.
  rewrite tsubst_1; reflexivity || omega.
Qed.

(* Terms where all variables are < n *)

Inductive cterm n : term -> Prop :=
  | cterm_var : forall i, i < n -> cterm n (Tvar i)
  | cterm_zero : cterm n (Tzero)
  | cterm_succ : forall u, cterm n u -> cterm n (Tsucc u)
  | cterm_plus : forall u v, cterm n u -> cterm n v -> cterm n (Tplus u v)
  | cterm_mult : forall u v, cterm n u -> cterm n v -> cterm n (Tmult u v)
.

Lemma cterm_1 : forall n t, cterm n t -> forall n', n <= n' -> cterm n' t.
Proof.
induction t; intros.
rewrite H0.


  (* TODO *)
(*Admitted.*)

Lemma cterm_2 : forall n t, cterm n t -> forall k, tlift k t n = t.
Proof.
  (* TODO *)
Admitted.

Lemma cterm_3 : forall n t, cterm n t -> forall t' j, n <= j -> tsubst j t' t = t.
Proof.
  (* TODO *)
Admitted.

Lemma cterm_4 : forall n t, cterm (S n) t ->
  forall t', cterm 0 t' -> cterm n (tsubst n t' t).
Proof.
  (* TODO *)
Admitted.

(* Formulas *)

Inductive formula :=
  | Fequal : term -> term -> formula
  | Ffalse : formula
  | Fand : formula -> formula -> formula
  | For : formula -> formula -> formula
  | Fimplies : formula -> formula -> formula
  | Fexists : formula -> formula
  | Fforall : formula -> formula
.

(* Add n to all variables of t >= k *)

Fixpoint flift n A k :=
  match A with
    | Fequal u v => Fequal (tlift n u k) (tlift n v k)
    | Ffalse => Ffalse
    | Fand B C => Fand (flift n B k) (flift n C k)
    | For B C => For (flift n B k) (flift n C k)
    | Fimplies B C => Fimplies (flift n B k) (flift n C k)
    | Fexists B => Fexists (flift n B (S k))
    | Fforall B => Fforall (flift n B (S k))
  end
.

Lemma flift_1 : forall A n n' k k', k <= k' -> k' <= k + n ->
  flift n' (flift n A k) k' = flift (n' + n) A k.
Proof.
  induction A; intros; simpl; f_equal; auto.
  apply tlift_1; assumption.
  apply tlift_1; assumption.
  apply IHA; omega.
  apply IHA; omega.
Qed.

Lemma flift_2 : forall A n n' k k', k' <= k ->
  flift n' (flift n A k) k' = flift n (flift n' A k') (n' + k).
Proof.
  induction A; intros; simpl; f_equal; auto.
  apply tlift_2; assumption.
  apply tlift_2; assumption.
  replace (S (n' + k)) with (n' + S k) by omega.
  apply IHA; omega.
  replace (S (n' + k)) with (n' + S k) by omega.
  apply IHA; omega.
Qed.

(* Replace variable x by (tlift x t' 0) in A *)

Fixpoint fsubst x t' A :=
  match A with
    | Fequal u v => Fequal (tsubst x t' u) (tsubst x t' v)
    | Ffalse => Ffalse
    | Fand B C => Fand (fsubst x t' B) (fsubst x t' C)
    | For B C => For (fsubst x t' B) (fsubst x t' C)
    | Fimplies B C => Fimplies (fsubst x t' B) (fsubst x t' C)
    | Fexists B => Fexists (fsubst (S x) t' B)
    | Fforall B => Fforall (fsubst (S x) t' B)
  end
.

Lemma fsubst_1 : forall A x t' n k, k <= x -> x <= k + n ->
  fsubst x t' (flift (S n) A k) = flift n A k.
Proof.
  induction A; intros; simpl; f_equal; auto.
  apply tsubst_1; assumption.
  apply tsubst_1; assumption.
  apply IHA; omega.
  apply IHA; omega.
Qed.

Lemma fsubst_2 : forall A x t' n k, k <= x ->
  flift n (fsubst x t' A) k = fsubst (n + x) t' (flift n A k).
Proof.
  induction A; intros; simpl; f_equal; auto.
  apply tsubst_2; assumption.
  apply tsubst_2; assumption.
  replace (S (n + x)) with (n + S x) by omega.
  apply IHA; omega.
  replace (S (n + x)) with (n + S x) by omega.
  apply IHA; omega.
Qed.

Lemma fsubst_3 : forall A x t' n k,
  flift n (fsubst x t' A) (x + k) =
  fsubst x (tlift n t' k) (flift n A (S (x + k))).
Proof.
  induction A; intros; simpl; f_equal; auto.
  apply tsubst_3; assumption.
  apply tsubst_3; assumption.
  change (S (x + k)) with (S x + k); now apply IHA.
  change (S (x + k)) with (S x + k); now apply IHA.
Qed.

Lemma fsubst_4 : forall A x t' y u',
  fsubst (x + y) u' (fsubst x t' A) =
  fsubst x (tsubst y u' t') (fsubst (S (x + y)) u' A).
Proof.
  induction A; intros; simpl; f_equal; auto.
  apply tsubst_4; assumption.
  apply tsubst_4; assumption.
  change (S (x + y)) with (S x + y); now apply IHA.
  change (S (x + y)) with (S x + y); now apply IHA.
Qed.

(* Formulas where all variables are < n *)

Inductive cformula n : formula -> Prop :=
  | cformula_equal : forall u v,
    cterm n u -> cterm n v -> cformula n (Fequal u v)
  | cformula_false : cformula n Ffalse
  | cformula_and : forall B C,
    cformula n B -> cformula n C -> cformula n (Fand B C)
  | cformula_or : forall B C,
    cformula n B -> cformula n C -> cformula n (For B C)
  | cformula_implies : forall B C,
    cformula n B -> cformula n C -> cformula n (Fimplies B C)
  | cformula_exists : forall B,
    cformula (S n) B -> cformula n (Fexists B)
  | cformula_forall : forall B,
    cformula (S n) B -> cformula n (Fforall B)
.

Lemma cformula_1 : forall n A, cformula n A ->
  forall n', n <= n' -> cformula n' A.
Proof.
  (* TODO *)
Admitted.

Lemma cformula_2 : forall n A, cformula n A -> forall k, flift k A n = A.
Proof.
  (* TODO *)
Admitted.

Lemma cformula_3 : forall n A, cformula n A ->
  forall t' j, n <= j -> fsubst j t' A = A.
Proof.
  (* TODO *)
Admitted.

Lemma cformula_4 : forall n A, cformula (S n) A ->
  forall t', cterm 0 t' -> cformula n (fsubst n t' A).
Proof.
  (* TODO *)
Admitted.

(* Natural deduction rules (intuitionistic) *)

Definition elift n e k := map (fun A => flift n A k) e.

Inductive ND : list formula -> formula -> Prop :=
  | NDaxiom : forall e A, In A e -> ND e A
  | NDfalse_elim : forall e, ND e Ffalse -> forall A, ND e A
  | NDand_intro : forall e B C, ND e B -> ND e C -> ND e (Fand B C)
  | NDand_elim1 : forall e B C, ND e (Fand B C) -> ND e B
  | NDand_elim2 : forall e B C, ND e (Fand B C) -> ND e C
  | NDor_intro1 : forall e B C, ND e B -> ND e (For B C)
  | NDor_intro2 : forall e B C, ND e C -> ND e (For B C)
  | NDor_elim : forall e A B C,
    ND e (For B C) -> ND (B::e) A -> ND (C::e) A -> ND e A
  | NDimpl_intro : forall e B C, ND (B::e) C -> ND e (Fimplies B C)
  | NDimpl_elim : forall e B C, ND e (Fimplies B C) -> ND e B -> ND e C
  | NDforall_intro : forall e B,
    ND (elift 1 e 0) B -> ND e (Fforall B)
  | NDforall_elim : forall e B t j, cterm j t ->
    ND e (Fforall B) -> ND e (fsubst 0 t B)
  | NDexists_intro : forall e B t j, cterm j t ->
    ND e (fsubst 0 t B) -> ND e (Fexists B)
  | NDexists_elim : forall e A B,
    ND e (Fexists B) -> ND (B::elift 1 e 0) (flift 1 A 0) -> ND e A
.

(* Auxiliary connectives and admissible rules *)

(* TODO: remplacer les quatre paramètres suivants par des définitions *)
Parameter Ftrue : formula.
Parameter Fnot : formula -> formula.
Parameter Fequiv : formula -> formula -> formula.
Parameter nFforall : nat -> formula -> formula.

Lemma NDtrue : forall e, ND e Ftrue.
Proof.
  (* TODO *)
Admitted.

Lemma NDnot_intro : forall e A, ND (A::e) Ffalse -> ND e (Fnot A).
Proof.
  (* TODO *)
Admitted.

Lemma NDnot_elim : forall e A, ND e A -> ND e (Fnot A) -> ND e Ffalse.
Proof.
  (* TODO *)
Admitted.

Lemma NDequiv_intro : forall e A B,
  ND (A::e) B -> ND (B::e) A -> ND e (Fequiv A B).
Proof.
  (* TODO *)
Admitted.

Lemma nFforall_1 : forall n x t A,
  fsubst x t (nFforall n A) = nFforall n (fsubst (n + x) t A).
Proof.
  (* TODO *)
Admitted.

(* Notations *)

Reserved Notation "A ==> B" (at level 90).
Reserved Notation "# n" (at level 2).

Notation "A /\ B" := (Fand A B) : pa_scope.
Notation "A \/ B" := (For A B) : pa_scope.
Notation "A ==> B" := (Fimplies A B) : pa_scope.
Notation "~ A" := (Fnot A) : pa_scope.
Notation "x = y" := (Fequal x y) : pa_scope.
Notation "x + y" := (Tplus x y) : pa_scope.
Notation "x * y" := (Tmult x y) : pa_scope.
Notation "# n" := (Tvar n) : pa_scope.

Delimit Scope pa_scope with pa.
Bind Scope pa_scope with term.
Bind Scope pa_scope with formula.

Close Scope nat_scope.
Close Scope type_scope.
Close Scope core_scope.
Open Scope pa_scope.
Open Scope core_scope.
Open Scope type_scope.
Open Scope nat_scope.

(* Peano axioms *)

Inductive Ax : formula -> Prop :=
  | pa_refl : Ax (nFforall 1 (#0 = #0))%pa
  | pa_sym : Ax (nFforall 2 (#1 = #0 ==> #0 = #1))%pa
  | pa_trans : Ax (nFforall 3 (#2 = #1 /\ #1 = #0 ==> #2 = #0))%pa
  | pa_compat_s : Ax (nFforall 2 (#1 = #0 ==> Tsucc #1 = Tsucc #0))%pa
  | pa_compat_plus_l : Ax (nFforall 3 (#2 = #1 ==> #2 + #0 = #1 + #0))%pa
  | pa_compat_plus_r : Ax (nFforall 3 (#1 = #0 ==> #2 + #1 = #2 + #0))%pa
  | pa_compat_mult_l : Ax (nFforall 3 (#2 = #1 ==> #2 * #0 = #1 * #0))%pa
  | pa_compat_mult_r : Ax (nFforall 3 (#1 = #0 ==> #2 * #1 = #2 * #0))%pa
  | pa_plus_O : Ax (nFforall 1 (Tzero + #0 = #0))%pa
  | pa_plus_S : Ax (nFforall 2 (Tsucc #1 + #0 = Tsucc (#1 + #0)))%pa
  | pa_mult_O : Ax (nFforall 1 (Tzero * #0 = Tzero))%pa
  | pa_mult_S : Ax (nFforall 2 (Tsucc #1 * #0 = (#1 * #0) + #0))%pa
  | pa_inj : Ax (nFforall 2 (Tsucc #1 = Tsucc #0 ==> #1 = #0))%pa
  | pa_discr : Ax (nFforall 1 (~ Tzero = Tsucc #0))%pa
  | pa_ind : forall A n, cformula (S n) A ->
    Ax (nFforall n (
      fsubst 0 Tzero A /\
      Fforall (A ==> fsubst 0 (Tsucc #0) (flift 1 A 1)) ==> Fforall A
    ))%pa
.

(* Definition of theorem *)

Definition Th T :=
  exists axioms, (forall A, In A axioms -> Ax A) /\ ND axioms T.

(* Example of theorem *)

(* TODO: remplacer la formula par l'encodage du lemme n_Sn de la bibliothèque
   standard de Coq *)
Lemma HA_n_Sn : Th Ffalse.
Proof.
  (* TODO *)
Admitted.

(* Interpretation of terms *)

Fixpoint tinterp b t :=
  match t with
    | Tvar j => nth j b O
    | Tzero => O
    | Tsucc u => S (tinterp b u)
    | Tplus u v => tinterp b u + tinterp b v
    | Tmult u v => tinterp b u * tinterp b v
  end
.

Lemma tinterp_1 : forall t' t b1 b2,
  tinterp (b1 ++ b2) (tsubst (length b1) t' t) =
  tinterp (b1 ++ (tinterp b2 t') :: b2) t.
Proof.
  (* TODO *)
Admitted.

Lemma tinterp_2 : forall t j, cterm j t ->
  forall b1 b2, j <= length b1 -> j <= length b2 ->
  (forall i, i < j -> nth i b1 0 = nth i b2 0) ->
  tinterp b1 t = tinterp b2 t.
Proof.
  (* TODO *)
Admitted.

Lemma tinterp_3 : forall t b0 b1 b2,
  tinterp (b0++b2) t =
  tinterp (b0++b1++b2) (tlift (length b1) t (length b0)).
Proof.
  (* TODO *)
Admitted.

(* Interpretation of formulas *)

Fixpoint finterp b A :=
  match A with
    | Fequal u v => tinterp b u = tinterp b v
    | Ffalse => False
    | Fand B C => finterp b B /\ finterp b C
    | For B C => finterp b B \/ finterp b C
    | Fimplies B C => finterp b B -> finterp b C
    | Fexists B => exists n, finterp (n::b) B
    | Fforall B => forall n, finterp (n::b) B
  end
.

Lemma finterp_1 : forall t' A b1 b2,
  finterp (b1 ++ b2) (fsubst (length b1) t' A) <->
  finterp (b1 ++ (tinterp b2 t') :: b2) A.
Proof.
  (* TODO *)
Admitted.

Lemma finterp_2 : forall A j, cformula j A ->
  forall b1 b2, j <= length b1 -> j <= length b2 ->
  (forall i, i < j -> nth i b1 0 = nth i b2 0) ->
  (finterp b1 A <-> finterp b2 A).
Proof.
  (* TODO *)
Admitted.

Lemma finterp_3 : forall A b0 b1 b2,
  finterp (b0 ++ b2) A <->
  finterp (b0 ++ b1 ++ b2) (flift (length b1) A (length b0)).
Proof.
  (* TODO *)
Admitted.

(* Soundess of deduction rules *)

Lemma ND_soundness : forall e A, ND e A ->
  forall b, (forall B, In B e -> finterp b B) -> finterp b A.
Proof.
  (* TODO *)
Admitted.

Lemma Ax_soundness : forall A, Ax A -> forall b, finterp b A.
Proof.
  (* TODO *)
Admitted.

Theorem coherence : ~Th Ffalse.
Proof.
  (* TODO *)
Admitted.
