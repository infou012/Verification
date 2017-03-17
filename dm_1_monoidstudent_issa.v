Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Import ListNotations.

(** Dans cet exercice, nous étudions la question de l'égalité dans les
    monoïdes. En mathématique (et donc en informatique), un monoïde
    est un ensemble [M] muni d'un élément unité [unit : M] et d'une
    opération de séquence [seq : M -> M -> M] vérifiant les équations
    suivantes:

    [[
       (unité à gauche:) 
           forall m: M, seq unit m = m

       (unité à droite:) 
           forall m: M, seq m unit = m

       (associativité:) 
           forall m n o: M,
               seq m (seq n o) = seq (seq m n) o 
    ]]

    Par exemple, les entiers naturels [nat] forment un monoïde
    (commutatif, de surcroît) pour l'unité [0 : nat] et l'addition 
    [+ : nat -> nat -> nat]. *)

Lemma nat_left_unit: forall n: nat, 0 + n = n.
Proof. trivial. Qed.

Lemma nat_right_unit: forall n: nat, n + 0 = n.
Proof. now induction n. Qed.

Lemma nat_assoc: forall m n o: nat, m + (n + o) = (m + n) + o.
Proof. now induction m; auto; simpl; intros; rewrite IHm. Qed.

(** QUESTION [difficulté [*] / longueur [*]]

    Montrer que les listes forment également un monoïde (non
    commutatif) pour l'unité [nil : list A] et la concaténation
    [++ : list A -> list A -> list A]. *)



Lemma list_left_unit {A}: forall l: list A, [] ++ l = l.
Proof. 
  intro.
  induction l; simpl; auto.
Qed.

Lemma list_right_unit {A}: forall l: list A, l ++ [] = l.
Proof. 
  apply app_nil_r.
Qed.

Lemma list_assoc {A}: forall (l m n: list A), (l ++ m) ++ n = l ++ (m ++ n).
Proof. 
  apply app_assoc_reverse. 
Qed.

(** Dans ce sujet, on s'intéresse à la question de savoir si deux
    expressions [e1] et [e2] de type [M] sont égales. *)

(** QUESTION  [difficulté [*] / longueur [***]]

    Prouver que les deux expressions suivantes, écrites
    dans le monoïde des listes, sont égales: *)
SearchAbout "++".

Example list_eq {A}: forall (x y z: list A),
    (x ++ (y ++ [])) ++ (z ++ [])
        = 
    (x ++ []) ++ ([] ++ y) ++ z.
Proof.
  intros.
  induction x.
   + simpl.
     induction y.
     * simpl. apply list_right_unit.
     * simpl. rewrite IHy. reflexivity.
   + simpl. rewrite IHx. simpl. reflexivity.

Qed.

(** Plutôt que de faire une telle preuve à chaque problème, nous
    allons construire une _procédure de décision_ résolvant le
    problème de l'égalité pour n'importe quelle équation et sur
    n'importe quel monoïde. *)

(** * Expressions *)

(** Pour cela, la première étape consiste à décrire, dans Coq, la
    syntaxe de telles équations. Pour représenter les variables de ces
    équations, nous utilisons des identifiants : *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id x1 x2 :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(** Par exemple, on défini (arbitrairement) les variables [U] à [Z] de
    la façon suivante: *)

Definition U : id := Id 0.
Definition V : id := Id 1.
Definition W : id := Id 2.
Definition X : id := Id 3.
Definition Y : id := Id 4.
Definition Z : id := Id 5.

(** On peut associer des valeurs Coq à des identifiants par le moyen
    d'un _environnement_ : *)

Definition env (A: Type) := id -> A.

Definition update {A}(e: env A)(x: id)(v: A): env A := 
  fun y => if beq_id x y then v else e y.

Notation "m [ x |-> v ]" := (update m x v) 
                              (at level 10, x, v at next level).

(** Une expression dans un monoïde correspond alors à une variable
    [AId], à l'unité [Unit] du monoïde ou à la séquence [Seq] du
    monoïde. *)

Inductive exp: Type :=
| AId: id -> exp
| Unit: exp
| Seq: exp -> exp -> exp.

(** On note [e1 # e2] la séquence [Seq e1 e2] et [`X] le terme [AId X]. *)

Infix "#" := Seq 
               (right associativity, at level 60, only parsing).
Notation "` X" := (AId X) 
               (at level 5, only parsing).

Reserved Notation "e1 '~' e2" (at level 65).

(** Deux expressions [e1] et [e2] sont égales, suivant les équations
du monoïde, si et seulement ils satisfont la relation d'équivalence
suivante, ie. si l'on peut construire une preuve de [e1 ~ e2]: *)

Inductive eq: exp -> exp -> Prop :=
| mon_left_id: forall e, Unit # e ~ e
| mon_right_id: forall e, e # Unit ~ e
| mon_assoc: forall e f g, (e # f) # g ~ e # (f # g)

| mon_refl: forall e, e ~ e
| mon_sym: forall e f, e ~ f -> f ~ e
| mon_trans: forall e f g, e ~ f -> f ~ g -> e ~ g
| mon_congr: forall e f g h, e ~ g -> f ~ h -> e # f ~ g # h

where "e1 '~' e2" := (eq e1 e2).

(** QUESTION  [difficulté [*] / longueur [***]]

    Prouver l'équivalence suivante: *)

Example mon_exp_eq:
    (`X # (`Y # Unit)) # (`Z # Unit)
        ~ 
    (`X # Unit) # (Unit # `Y) # `Z.
Proof.
  assert (((`X # (`Y # Unit)) # (`Z # Unit)) ~
  (`X # ((`Y # Unit) # (`Z # Unit)))).    
  - apply mon_assoc.
  - admit.  
Qed.

(** Le type [exp] nous permet ainsi de représenter une expression
    quelconque d'un monoïde tandis que [~] capture précisement les
    équations que vérifie ce monoïde. La preuve [mon_exp_eq] ci-dessus
    s'applique ainsi à _tous_ les monoïdes concevables: il s'agit
    d'une preuve "générique".  *)

(** Cependant, la preuve en elle-même consiste à créer un témoin de
    l'équivalence par le truchement des constructeurs du type [~]:
    pour des preuves non-triviales, cela nécessitera de construire des
    témoins de preuves en mémoire, ralentissant voir rendant
    impossible l'effort de preuve. *)

(** * Normalisation par évaluation *)

(** Nous allons remplacer la construction manuelle de ces témoins de
    preuves par un _programme_ calculant ces témoins. En prouvant la
    correction de ce programme, on obtient alors la correction de
    notre procédure de décision. *)

(** On remarque que nos expressions s'interprètent naturellement dans
    le monoïde des fonctions de domaine [exp] et de co-domaine [exp],
    où l'unité correspond à la fonction identité et où la séquence
    correspond à la composition de fonctions: *)

Definition sem_exp := exp -> exp.

Notation sem_exp_unit := (fun x => x) 
                           (only parsing).
Notation sem_exp_seq e1 e2 := (fun x => e1 (e2 x))
                           (only parsing).

Fixpoint eval (c: exp): sem_exp :=
  match c with
  | Unit => sem_exp_unit
  | Seq e1 e2 => sem_exp_seq (eval e1) (eval e2)
  | AId i => fun e => `i # e
  end.


(** Étant donné un [sem_exp], on obtient une expression [exp] par
    application à l'unité. Par composition de l'évaluation et de la
    réification, on obtient une procédure de normalisation des
    expressions. *)

Definition reify (f: sem_exp): exp := f Unit.

Definition norm (e: exp): exp := reify (eval e).

(** Il s'agit de prouver que les termes ainsi obtenus sont
    effectivement des formes normales. Formellement, il s'agit de
    prouver la correction de notre procédure, ie. si deux expressions
    sont identifiées par [norm] alors elles sont équivalentes par
    l'équivalence [~]:

    [[
    Lemma soundness:
          forall e1 e2, norm e1 = norm e2 -> e1 ~ e2.
    ]] 

    et, inversement, il s'agit aussi de prouver la complétude de notre
    procédure, ie. si deux expressions sont équivalentes par [~] alors
    elles sont identifiées par [norm]: 

    [[
    Lemma completeness:
          forall e1 e2, e1 ~ e2 -> norm e1 = norm e2.
    ]]
    *)

(** QUESTION  [difficulté [**] / longueur [**]]

    À cette fin, prouvez les trois lemmes techniques suivants: *)

Print eq.

Lemma yoneda: 
  forall e e', e # e' ~ eval e e'.
Proof.
  intros.
  induction e.
  + simpl. apply mon_refl.
  + simpl. apply mon_left_id.
  + simpl.  
    inversion IHe1.
    - simpl. replace (Seq (Seq Unit e2) e') with (Seq e2 e').
      assumption.
      admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
Qed.

Lemma pre_soundness: 
  forall e, e ~ norm e.
Proof.
  intro e.
  eapply mon_trans.
  eapply mon_sym. eapply mon_right_id.
  unfold norm, reify.
  apply yoneda.
Qed.

Lemma pre_completeness: 
  forall e1 e2, e1 ~ e2 -> forall e', eval e1 e' = eval e2 e'.
Proof.
  intros e1 e2 H e'.
  induction H; try easy.
  rewrite IHeq1. rewrite IHeq2.
  reflexivity. simpl.
  SearchPattern ( _ = _).
  rewrite IHeq2.
  (* f_equal. *)
  admit.
Qed.

(** QUESTION [difficulté [***] / longueur [*]]

    À partir des résultats techniques ci-dessus, complétez
    les théorèmes suivants: *)

Theorem soundness:
  forall e1 e2, norm e1 = norm e2 -> e1 ~ e2.
Proof.
  intros.
  unfold norm, reify in H.
  (** AAAAAAAAAAAAHHHHH **)
  (* apply pre_completeness in H.*)
  
 (* induction e1.
  - simpl in H. apply mon_sym. *)
    admit.
Qed.

Theorem completeness: 
  forall e1 e2, e1 ~ e2 -> norm e1 = norm e2.
Proof.
  intros. apply pre_completeness. assumption.
Qed.


(** QUESTION [difficulté [***] / longueur [*]]

    Ces résultats ne servent pas seulement à s'assurer de la validité
    de notre programme, ils nous permettent de donner une preuve
    triviale à des problèmes d'égalité. Par exemple, prouvez le lemme
    suivant de façon concise: *)

Example non_trivial_equality:
  Seq (`U # Unit) 
       (Seq (Unit # `V)
            (`W # 
                 (Seq (`X # `Y)
                      (`Z # Unit))))
    ~
  (Seq (AId U) 
       (Seq (Seq (Seq (AId V) Unit)
                 (Seq (AId W) Unit)) 
            (Seq (AId X) (Seq (AId Y) (AId Z))))).
Proof.
  apply soundness.
  unfold norm, reify. simpl. reflexivity.
Qed.

(** * Preuve par réflection *)

Variable A : Type.

(** Dans la section précédente, nous avons développé une procédure de
    décision vérifiée pour décider l'égalité d'expressions sur un
    monoïde quelconque. Nous allons désormais exploiter cet outil pour
    décider de l'égalité dans le cas particulier du monoïde des
    listes. *)

(** À cette fin, nous donnons une interprétation des expressions vers
    les listes, où l'unité est traduite vers [nil], la séquence est
    traduite vers la concaténation [++] et l'interprétation des
    variables est donnée par l'environnement. *)

Fixpoint interp (m: env (list A))(e: exp): list A :=
  match e with
  | Unit => []
  | Seq a b => interp m a ++ interp m b
  | AId x => m x
  end.

(** Cette fonction d'interprétation nous permet de remplacer (de façon
    calculatoirement transparente) des expressions Coq portant sur le
    monoïde des listes vers des expressions [exp] portant sur un
    monoïde quelconque. *)

Definition empty: env (list A) := fun _ => [].

Remark trivial_eq: forall (x y z: list A),
    let m := empty [ X |-> x ][ Y |-> y ][ Z |-> z ] in

    (x ++ (y ++ [])) ++ (z ++ [])
       = 
    interp m ((`X # (`Y # Unit)) # (`Z # Unit)).

Proof. reflexivity. Qed.


(** QUESTION [difficulté [**] / longueur [**]]

    L'interprétation [interp] est _correcte_ si elle respecte les
    égalités des monoïdes. Prouvez que c'est effectivement le cas. *)

Lemma interp_proper: forall m e e', e ~ e' -> interp m e = interp m e'.
Proof.
  intros.
  induction H; try auto.
  - simpl. SearchAbout "app_". apply app_nil_r.
  - simpl. apply app_assoc_reverse.
  - simpl. rewrite IHeq1. rewrite IHeq2. auto.
  - simpl. rewrite IHeq1. rewrite IHeq2. auto.
Qed.

(** QUESTION [difficulté [***] / longueur [**]]

    En exploitant le lemme [interp_proper] et la correction de la
    procédure de décision, donnez des preuves concises des égalités
    suivantes. *)

Example list_eq2: forall (x y z: list A),
    (x ++ (y ++ [])) ++ (z ++ [])
        = 
    (x ++ []) ++ ([] ++ y) ++ z.
Proof.
  intros.
  set (m := empty [ X |-> x ][ Y |-> y ][ Z |-> z]).
  change ((x ++ (y ++ [])) ++ (z ++ [])) 
  with (interp m ((`X # (`Y # Unit)) # (`Z # Unit))).
  change ((x ++ []) ++ ([] ++ y) ++ z)
  with (interp m ((`X # Unit) # (Unit # `Y) # `Z)).
  apply interp_proper.
  apply soundness. compute. reflexivity.  
Qed.

Example list_eq3 : forall (u: list A) v w x y z, 
    u ++ ([] ++ v ++ []) ++ w ++ x ++ (y ++ []) ++ z
      = 
    u ++ ((v ++ [] ++ w) ++ x ++ y) ++ (z ++ []) ++ [].
Proof.
  intros.
  set (m := empty [ U |-> u ][ V |-> v ][ W |-> w] [X |-> x ][ Y |-> y ][ Z |-> z]).
  change (u ++ ([] ++ v ++ []) ++ w ++ x ++ (y ++ []) ++ z) 
  with (interp m (`U # (Unit # (AId V)# Unit) # (AId W) # (AId X) #
                   ((AId Y) # Unit) # (AId Z))).
  change (u ++ ((v ++ [] ++ w) ++ x ++ y) ++ (z ++ []) ++ [])
  with (interp m (`U # (((AId V) # Unit # (AId W)) # (AId X) # (AId Y))
                   # ((AId Z) # Unit) # Unit)).
  apply interp_proper.
  apply soundness. reflexivity.
Qed.