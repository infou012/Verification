Require Import Lists.List.
Import ListNotations.

(** * Exercise 1: *)

Section Ex1.

(** Implement a datatype [Fml] of propositional formulas parameterized
over [P : Type]. *)

Inductive Fml (P: Type): Type :=
| Atom  : P -> Fml P
| Neg   : Fml P -> Fml P
| Or    : Fml P -> Fml P -> Fml P
| And   : Fml P -> Fml P -> Fml P
| Impl  : Fml P -> Fml P -> Fml P.


End Ex1.

(** * Exercise 2: recursion over lists *)

Section Ex2.

Section FoldList.

Variable A X: Type.

(** Define the signature functor [sigma_list] of lists as an inductive
type *)

Inductive sigma_list X :=
| OpNil : sigma_list X
| OpCons : A -> X -> sigma_list X.

Variable alpha : sigma_list X -> X.

(** Implement a function [fold_list : list A -> X] *)

Fixpoint fold_list (l: list A): X :=
  match l with
  | [] => alpha (OpNil _)
  | a :: xs => alpha (OpCons _ a (fold_list xs))
  end.

End FoldList.

Check fold_right.

(** Implement a function [length : list A -> nat] using [fold_list] *)

Definition length {A} :=
  fold_list A nat (fun xs => match xs with
                        | OpNil => 0
                        | OpCons _ n => S n
                        end).

Compute (length (1 :: 2 :: 3 :: 4 :: [])).

End Ex2.

(** * Exercise 3: recursion over trees *)

Section Ex3. 

Inductive tree : Type := 
| Leaf : tree
| Node : nat -> tree -> tree -> tree.

Inductive sigma_tree (X: Type): Type := 
| OpLeaf : sigma_tree X
| OpNode : nat -> X -> X -> sigma_tree X.

Section FoldTree.

Variable X: Type.
Variable alpha : sigma_tree X -> X.

(** Implement a function [fold_tree : tree -> X] *)

Fixpoint fold_tree (t: tree): X := 
    match t with
  | Leaf => alpha (OpLeaf _)
  | Node n l r => alpha (OpNode _ n (fold_tree l) 
                                   (fold_tree r))
  end.

End FoldTree.

Check fold_tree.

(** Implement a function [height : tree -> nat] that computes the
maximal height of a tree *)

Definition height :=
  fold_tree nat
            (fun xs => match xs with
                    | OpLeaf => 0
                    | OpNode _ lh rh => 1 + max lh rh
                    end).


Compute (height (Node 3 (Node 0 Leaf Leaf) (Node 1 (Node 2 Leaf Leaf) Leaf))).

End Ex3.

(** * Exercise 4: Initial algebra semantics *)

Section Ex4.

(** Implement [out_tree : tree -> sigma_tree tree] *)

Definition out_tree (t: tree): sigma_tree tree :=
  match t with
  | Leaf => OpLeaf _
  | Node n l r => OpNode _ n l r
  end.

(** Implement the functorial map [sigma_tree_map : (X -> Y) ->
sigma_tree X -> sigma_tree Y] *)

Definition sigma_tree_map {X Y} (f: X -> Y)
           (xs: sigma_tree X): sigma_tree Y := 
  match xs with
  | OpLeaf => OpLeaf _
  | OpNode n l r => OpNode _ n (f l) (f r)
  end.

End Ex4.

(** * Exercise 5: Uniform induction over natural numbers *)

Section Ex5.

Hypothesis P: nat -> Type.

Inductive sigma_ind_nat: nat -> Type :=
| OpIndZ : 
    sigma_ind_nat 0
| OpIndS: forall n,
    P n -> sigma_ind_nat (S n).

Fixpoint nat_rect' 
         (IH: forall n, sigma_ind_nat n -> P n)
         (n: nat): P n :=
  match n with
  | 0 => IH 0 OpIndZ
  | S n => IH (S n) (OpIndS n (nat_rect' IH n))
  end.

End Ex5.

(** * Exercise 6: recursion from induction *)

Section Ex6.

Section FoldTree'.

Variable X : Type.
Variable alpha : sigma_tree X -> X.

(** Implement [fold_tree' : tree -> X] from [tree_rect] *)

Definition fold_tree' : tree -> X
  := @tree_rect (fun _ => X) 
                (alpha (OpLeaf _)) 
                (fun n l xl r xr => alpha (OpNode _ n xl xr)).

End FoldTree'.

(** Reimplement [height : tree -> nat] using this [fold_tree'] *)

Definition height' :=
  fold_tree' nat 
            (fun xs => match xs with
                    | OpLeaf => 0
                    | OpNode _ lh rh => 1 + max lh rh
                    end).


Compute (height' (Node 3 (Node 0 Leaf Leaf) (Node 1 (Node 2 Leaf Leaf) Leaf))).

End Ex6.

(** * Exercise 7: induction over tree *)

Section Ex7.

(** Implement the uniform induction principle over trees *)

Section TreeRect.

Hypothesis P: tree -> Type.

Inductive sigma_ind_tree: tree -> Type :=
| OpIndLeaf : 
    sigma_ind_tree Leaf
| OpIndNode : forall n l r,
    P l -> P r -> sigma_ind_tree (Node n l r).

Fixpoint tree_rect'
         (IH: forall t, sigma_ind_tree t -> P t)
         (t : tree): P t := 
  match t with
  | Leaf => IH Leaf OpIndLeaf
  | Node n l r => IH (Node n l r)
                    (OpIndNode n l r
                               (tree_rect' IH l) 
                               (tree_rect' IH r))
  end.

End TreeRect.

Section Ex7.

(** * Exercise 8: induction over rose trees *)

Section Ex8.

Inductive rosetree :=
| rosenode : nat -> list rosetree -> rosetree.

(** Implement induction over [rosetree] *)

Fixpoint rosetree_ind' 
         (P: rosetree -> Prop)
         (Pl: list rosetree -> Prop)
         (IH1: forall n ts, Pl ts -> P (rosenode n ts))
         (IH2: Pl [])
         (IH3: forall t ts, P t -> Pl ts -> Pl (t :: ts))
         (t: rosetree): P t.
destruct t; apply IH1.
induction l.
- apply IH2.
- apply IH3.
  + eapply rosetree_ind'; eauto.
  + apply IHl.
Show Proof.
Defined.


End Ex8.