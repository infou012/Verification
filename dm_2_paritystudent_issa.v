Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Axiom admit: forall {X},  X.

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

(** Dans cet exercice, nous étendons la sémantique du langage Imp
    étudié en cours, étendons sa logique de programme et vérifions la
    correction d'un programme écrit dans ce système. *)

(** * Variables *)

(** Comme en cours, nous modélisons les variables du langage par un
    type [id] dont nous nommons (arbitrairement) 3 éléments [X], [Y]
    et [Z]. *)

Inductive id : Type :=
  | Id : nat -> id.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Definition beq_id x1 x2 :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.


Theorem beq_id_refl : forall x, beq_id x x = true.
Proof. now intros; destruct x; simpl; rewrite <- beq_nat_refl. Qed.

(** QUESTION [difficulté [*] / longueur [*]]

    [X] et [Y] étant définis, les lemmes suivants sont prouvables par
    simple _calcul_.  *)

Remark rq1: beq_id X X = true.
Proof. 
  apply beq_id_refl.
Qed.

Remark rq2: beq_id X Y = false.
Proof.
  simpl.
  auto.
Qed.

(** * Mémoire *)

(** Comme en cours, nous modélisons la mémoire par une fonction des
    identifiants vers les entiers. On accède donc au contenu de la
    mémoire [s] à l'adresse [x] par application [s x]. *)

Definition state := id -> nat.

Definition empty_state: state := fun _ => 0.

Definition update (s: state)(x: id)(n: nat) :=
  fun y => if beq_id x y then n else s y.

(** QUESTION [difficulté [**] / longueur [*]]

    Prouver les identités suivantes reliant l'extension de la mémoire
    et l'accès à la mémoire: *)


Lemma update_eq : forall s x v,
    update s x v x = v.
Proof. 
  intros. induction v;
  unfold update; rewrite beq_id_refl; reflexivity.
Qed.

Lemma update_shadow : forall s v1 v2 x,
    update (update s x v1) x v2
  = update s x v2.
Proof.
  intros. unfold update; simpl.
  apply functional_extensionality.
  intro x0.
  case (beq_id x x0); auto.
Qed.

(** * Expressions booléennes *)

(** Les expressions booléennes permettent d'écrire des formules
    booléennes (avec [BTrue], [BFalse], [BNot] et [BAnd]) ainsi que
    des tests sur le contenu des variables ([BEq] et [BLe]). *)

Inductive bexp : Type :=
  | BTrue  : bexp
  | BFalse : bexp
  | BNot   : bexp -> bexp
  | BAnd   : bexp -> bexp -> bexp
  | BEq    : id -> nat -> bexp
  | BLe    : id -> nat -> bexp.

Fixpoint beval (st: state)(b : bexp) : bool :=
  match b with
  | BTrue      => true
  | BFalse     => false
  | BNot b1    => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  | BEq x n    => beq_nat (st x) n
  | BLe x n    => leb (st x) n
  end.

(** QUESTION [difficulté [*] / longueur [*]]

    Dériver le "ou logique" [BOr] à partir de [BNot] et [BAnd]
    (suivant la loi de De Morgan) puis prouver que sa sémantique est
    conforme à [orb], l'implémentation du "ou logique" en Coq.  *)


Definition BOr (b1 b2: bexp): bexp :=
  BNot (BAnd (BNot b1) (BNot b2)).

Lemma bor_correct: forall st b1 b2, 
    beval st (BOr b1 b2) = orb (beval st b1) (beval st b2).
Proof.
  intros. simpl. 
  SearchAbout "negb".
  rewrite negb_andb.
  rewrite negb_involutive.
  rewrite negb_involutive.
  reflexivity.
Qed.

(** QUESTION [difficulté [**] / longueur [***]]

    Prouver que la sémantique de [BLe'] défini ci-dessous est conforme
    à [leb], l'implémentation de la comparaison d'entiers dans Coq. *)

Definition BLe' (m: nat)(x: id): bexp :=
  BOr (BNot (BLe x m)) (BEq x m).

Lemma ble'_correct: forall st m x, beval st (BLe' m x) = leb m (st x).
Proof.
  intros.
  unfold BLe'.
  rewrite bor_correct.
  simpl.
  remember (leb m (st x)).
  destruct b.
  - apply orb_true_iff.
    symmetry in Heqb.
    apply leb_iff, le_lt_or_eq in Heqb.
    destruct Heqb.
    + left.
      now apply negb_true_iff, leb_correct_conv.
    + right.
      now apply beq_nat_true_iff.
  - apply orb_false_iff.
    symmetry in Heqb.
    apply leb_complete_conv in Heqb.
    split.
    + apply negb_false_iff. apply leb_correct.
      omega.
    + SearchAbout "beq_nat_fa".
      apply beq_nat_false_iff. 
      omega.
Qed.

(** * Commandes *)

(** Nous considérons le langage des commandes habituelles ([CSkip],
    [CSeq], [CWhile]) étendu avec une commande décrémentant une
    variable ([CDecr]). *)

Inductive com : Type :=
  | CSkip : com
  | CSeq : com -> com -> com
  | CWhile : bexp -> com -> com
  | CDecr : id -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '--'" :=
  (CDecr x) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).

(** QUESTION [difficulté [***] / longueur [*]]

    Compléter la sémantique du langage de commandes ci-dessous avec la
    sémantique de [CDecr]. *)

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,

  (*--------------------------------------*)
      SKIP / st \\ st

  | E_Seq : forall c1 c2 st st' st'',

      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
  (*--------------------------------------*)
      (c1 ;; c2) / st \\ st''
  | E_WhileEnd : forall b st c,

      beval st b = false ->
  (*--------------------------------------*)
      (WHILE b DO c END) / st \\ st
  | E_WhileLoop : forall st st' st'' b c,

      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
  (*--------------------------------------*)
      (WHILE b DO c END) / st \\ st''

                         
  | E_DECR : forall st st' x,
      update st x (st x - 1) = st' ->     
      (x--) / st \\ update st x (st x - 1)
      
      
  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** Dans ce langage, on peut ainsi écrire le programme suivant, qui
    teste la parité du contenu de la variable [X]: *)

Definition PARITY :=
 WHILE (BLe' 2 X) DO
       X-- ;; X--
 END.

(** QUESTION [difficulté [*] / longueur [*]]

    Prouver que, à partir d'un état mémoire où [X = 4], le résultat de la commande [X--]
    retourne un état où [X = 3]. *)

Example Decr_test: 
  X-- / update empty_state X 4 \\ update empty_state X 3.
Proof.
  set (m := update empty_state X 4).
  replace (update empty_state X 3) with (update m X (m X - 1)).
  - apply E_DECR with (update m X (m X - 1)). reflexivity.
  - 
    subst m. simpl.
    apply update_shadow.
Qed.

(** QUESTION [difficulté [**] / longueur [***]]

    Prouver que, à partir d'un état mémoire où [X = 4], le test de
    parité retourne [X = 0]. *)

Example PARITY_test: 
  PARITY / update empty_state X 4 \\ update empty_state X 0.
Proof.
  unfold PARITY.  
  apply E_WhileLoop with (update (update (update empty_state X 4) X 3) X 2).
  - easy.
  - apply E_Seq with (update (update empty_state X 4) X 3).
    + apply E_DECR with (update (update empty_state X 4) X 3).
      easy.
    + apply E_DECR with (update (update (update empty_state X 4) X 3) X 2).
      easy.
  - replace (update (update (update empty_state X 4) X 3) X 2) with
      (update empty_state X 2).
    apply E_WhileLoop with (update (update (update empty_state X 2) X 1)  X 0).
    + easy.
    + apply E_Seq with (update (update empty_state X 2) X 1).
      * apply E_DECR with (update (update empty_state X 2) X 1).
        easy.
      * apply E_DECR with (update (update (update empty_state X 2) X 1) X 0).
        easy.
    + replace (update (update (update empty_state X 2) X 1) X 0) with
      (update empty_state X 0).
      apply E_WhileEnd.
      easy.
      replace (update empty_state X 0) with
      (update (update empty_state X 1) X 0).
      apply eq_sym. f_equal. apply update_shadow. apply update_shadow.
    + replace (update empty_state X 2) with
      (update (update empty_state X 3) X 2).
      apply eq_sym. f_equal. apply update_shadow. apply update_shadow.
Qed.

(** * Logique de Hoare *)

(** Nous obtenons une logique de programme par la construction
    usuelle. *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80).

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
     c / st \\ st'  ->
     P st  -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
    (at level 90, c at next level).

(** À partir de ces définitions, nous pouvons spécifier le
    comportement des commandes grâce à la logique de programme. Pour
    [SKIP], [;;] et [WHILE], cela se traduit par les spécifications
    suivantes: *)

Axiom hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} -> P ->> P' ->
  {{P}} c {{Q}}.

Axiom hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} -> Q' ->> Q ->
  {{P}} c {{Q}}.

Axiom hoare_skip : forall P,
     {{P}} SKIP {{P}}.

Axiom hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} -> {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Axiom hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.

(** QUESTION [difficulté [***] / longueur [*]]

    Sur le modèle de l'assignation (vu en cours), donner et prouver la
    spécification la plus précise possible pour l'opération de
    décrémentation. *)

Definition assn_sub X P : Assertion := 
  fun (st : state) => P (update st X (st X - 1)).

Notation "P '[' X '--]'" := (assn_sub X P) (at level 10).

Theorem hoare_decr : forall Q X,
    {{Q [X --]}}  X--  {{Q}}.

Proof.
  unfold hoare_triple.
  intros Q X st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ.
  assumption.
Qed.

(** * Preuve de correction *)

(** Nous souhaitons désormais prouver la correction du programme
    [PARITY] introduit précédemment. Pour cela, il nous faut traduire
    la spécification informelle de [PARITY] par une définition
    formelle dans Coq. *)

(** QUESTION {BONUS} [difficulté [*] / longueur [*]]

    Implémenter la fonction [parity] ci-dessous qui doit retourner [0]
    si son argument est pair et [1] si son argument est impaire. *)

SearchAbout "mod".

Fixpoint parity (x: nat): nat :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S n) => parity n
  end.

Eval compute in parity 3.
Eval compute in parity 8.

(** QUESTION {BONUS} [difficulté [**] / longueur [**]]

    Afin de prouver la correction de [PARITY] vis-à-vis de [parity],
    nous aurons besoin des deux lemmes techniques suivants. *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  intros.
  induction x.
  - easy.
  - SearchPattern (_ <= _ -> _).
    admit.    
Qed.


Lemma parity_lt_2 : forall x,
  not (2 <= x) ->
  parity x = x.
Proof.
  intros.
  induction x.
  + easy.
  + admit. 
Qed.

(** QUESTION {BONUS} [difficulté [***] / longueur [***]]

    À l'aide de ces résultats et des opérations de la logique de
    programme, prouver la correction de [PARITY]. *)

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
      PARITY
    {{ fun st => st X = parity m }}.
Proof.
  intros.
  apply hoare_consequence_pre 
      with (P' := fun st => parity (st X) = parity m).
  apply hoare_consequence_post
      with (Q' := fun st => parity (st X) = parity m /\ st X < 2).
  - (* Prove: {{ parity X = parity m }} PARITY {{ parity X = parity m /\ X < 2 }} *)
    unfold PARITY.
    admit.
  - (* Prove: parity X = parity m /\ X < 2 -> st X = parity m *)    
    unfold assert_implies.
    intros.
    destruct H as [H1 H2].
    rewrite <- H1.
    apply eq_sym.
    apply parity_lt_2.
    SearchPattern (~ _ <= _).
    apply lt_not_le. assumption.
  - (* Prove: X = m -> parity X = parity m *)
    unfold assert_implies.
    intros.
    rewrite <- H.
    reflexivity.
Qed.
