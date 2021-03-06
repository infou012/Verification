(** * A Foray into Certified Programming  *)

Require Import Lists.List.
Import ListNotations.

(** ** Scottish Certified Programming *)

Module McCompiler.

(** At this point, we are not scared of writing effectful programs in
    type theory. It is therefore tempting to make use of those
    dependent types for proving as well. The following application is
    based on a draft of James McKinna & Joel Wright entitled "A
    type-correct, stack-safe, provably correct, expression
    compiler". As suggested by the title, we are going to implement a
    correct-by-construction compiler from expressions to a stack
    machine. *)

(** *** Type-safe representation of programs *)

(** Because Coq's type system is extremely rich, we can in fact
    _absorb_ the type discipline of expressions in Coq. In programming
    terms, we define a datatype [exp] that represents only well-typed
    expressions. *)

Inductive typ := Nat | Bool.

Definition sem (T: typ): Type := 
  match T with
  | Nat => nat 
  | Bool => bool 
  end.

Inductive exp : typ -> Type :=
| val : forall {T}, sem T -> exp T
| plus : exp Nat -> exp Nat -> exp Nat
| ifte : forall{T}, exp Bool -> exp T -> exp T -> exp T.

(** As usual, we define the semantics of this language by
    interpretation within Coq: *)

Fixpoint eval {T} (e: exp T): sem T :=
  match e with
  | val _ v => v
  | plus e1 e2 => (eval e1) + (eval e2)
  | ifte _ b e1 e2 => if eval b then eval e1 else eval e2
  end.

(** *** Stack machine *)

(** Our stack machine will interpret a fixed set of opcodes,
    transforming input stack into output stack. A stack will contain
    values, ie. Booleans or integers. We can therefore describe
    well-typed stacks by identifying the type of each elements: *)


Definition stack_typ := list typ.

Inductive stack : stack_typ -> Type :=
| eps : stack nil
| cns : forall {T}{S}, sem T -> stack S -> stack (cons T S).


(** In particular, a non-empty stack allows us to peek at the top
    element and to take its tail *)

Definition top {T S}(s: stack (T :: S)): sem T :=
  match s with
  | cns _ _ t _ => t
  end.

Definition tail {T S}(s: stack (T :: S)): stack S :=
  match s with
  | cns _ _ _ s => s
  end.


(** Using an inductive family, we can once again garantee that
    instructions are only applied onto well-typed stacks: *)

Inductive code : stack_typ -> stack_typ -> Type :=
| skip : forall{S}, code S S
| seq : forall{S1 S2 S3}, code S1 S2 -> code S2 S3 -> code S1 S3
| PUSH : forall{T S}, sem T -> code S (T :: S)
| ADD : forall{S}, code (Nat :: Nat :: S) (Nat :: S)
| IFTE : forall{S S'}, code S S' -> code S S' -> code (Bool :: S) S'.

(** As a result, we can implement a (total) execution function for our
    stack machine: *)

Fixpoint exec {S S'} (c: code S S'): stack S -> stack S' :=
  match c with
  | skip _ => fun s => s
  | seq _ _ _ c1 c2 => fun s => exec c2 (exec c1 s)
  | PUSH _ _ v => fun s => cns v s
  | ADD _ =>
    fun s => 
      match s with
      | cns Nat _ a s' => 
        match s' with
        | cns Nat _ b s'' => @cns Nat _ (a + b) s''
        end
      end
  | IFTE S1 S2 c1 c2 => 
    fun s => 
      (match s with
       | cns Bool _ true s' => fun c1 c2 => exec c1 s'
       | cns Bool _ false s' => fun c1 c2 => exec c2 s'
       end) c1 c2
  end.


(** *** Compilation *)

(** The compiler from expressions to stack machine code is then
    straightforward, the types making sure that we cannot generate
    non-sensical opcodes (but this does not guarantee that we preserve
    the semantics!) *)

Fixpoint compile {T S} (e: exp T): code S (T :: S) :=
  match e with
  | val _ v => PUSH v
  | plus e1 e2 => seq (compile e2) (seq (compile e1) ADD)
  | ifte _ b e1 e2 => seq (compile b) (IFTE (compile e1) (compile e2))
  end.

(** *** Correctness *)

(** The correctness proof amounts to showing that the interpreter for
    expressions agrees with the result of executing the stack
    machine. Having baked the typing discipline in our input
    expressions and output machine codes, we can focus on proving only
    the meaningful cases. *)

Lemma correctness:
  forall {T S} (e: exp T) (s: stack S),
    cns (eval e) s = exec (compile e) s.
Proof.
intros T S e; generalize S.
induction e; simpl; intros; auto.
- now rewrite <- IHe2, <- IHe1.
- now
    rewrite <- IHe1;
    destruct (eval e1);
    rewrite <- ? IHe2, <- ? IHe3.
Qed.


End McCompiler.

(** ** French certified programming *)

Module MonsieurCompilateur.

(** To a veteran Coq programmer, the previous section is pure
    heresy. And, indeed, if you have tried to implement those
    functions by yourself, it may have been an epic struggle to merely
    _write_ the above functions, let alone prove their correctness.

    The pragmatic Coq programmer is more likely to define simply-typed
    datatypes and write simply-typed, partial programs, à la ML. The
    typing invariants are maintained on the side, through ad-hoc
    inductive relations. The correctness proofs must then bear with
    many useless cases, but this can be hidden away through
    automation. *)

(** *** Exercise: failure monad, 2 stars *)

(** In the following, we shall make use of the failure monad
    introduced in Lecture 3. *)

Definition failure (X: Type): Type := option X.
Definition error {X} (tt: unit): failure X := None.

(** Implement its associated operations: *)

Definition ret {X} (x: X): failure X :=
  Some x.

Definition bind {X Y}(mx: failure X)(k: X -> failure Y): failure Y :=
  match mx with
  | Some x => k x
  | None => error tt
  end.

Notation "'let!' x ':=' mx 'in' f" := 
  (bind mx (fun x => f)) (at level 50).

(** *** Expressions *)

(** Intuitively, we are dealing with a _dynamically-typed_ expression
    language. Values must therefore be _tagged_ by their run-time type: *)

Inductive value := 
| value_bool: bool -> value
| value_nat: nat -> value.

Inductive exp : Type :=
| val : value -> exp
| plus : exp -> exp -> exp
| ifte : exp -> exp -> exp -> exp.

(** Our evaluation function cannot be total anymore: it must deal with
    ill-typed values. *)

Fixpoint eval (e: exp): failure value :=
  match e with
  | val v => ret v
  | plus e1 e2 => 
    let! x := eval e1 in
    let! y := eval e2 in
    match x, y with
    | value_nat m, value_nat n => 
      ret (value_nat (m + n))
    | _, _ => error tt
    end
  | ifte b e1 e2 => 
    let! x := eval b in
    match x with
    | value_bool x =>
      if x then eval e1 else eval e2
    | _ => error tt
    end
  end.

(** To re-gain the invariants offered by typing, we define an
    inductive relation [wt_value] that classifies [value]s based on a
    type and an inductive relation [wt_exp] that classifies
    [exp]ressions based on a type. *)

Inductive typ := Nat | Bool.

Inductive wt_value: value -> typ -> Prop :=
| wt_val_bool: forall b, 

 (* ---------------------------- *)
    wt_value (value_bool b) Bool

| wt_val_nat: forall n, 

 (* ---------------------------- *)
    wt_value (value_nat n) Nat.

Inductive wt_exp: exp -> typ -> Prop :=
| wt_val: forall v ty, 

    wt_value v ty -> 
 (* ----------------- *)
    wt_exp (val v) ty

| wt_plus: forall e1 e2, 

    wt_exp e1 Nat -> 
    wt_exp e2 Nat -> 
 (* ----------------------- *)
    wt_exp (plus e1 e2) Nat

| wt_ifte: forall b e1 e2 ty, 

    wt_exp b Bool -> 
    wt_exp e1 ty -> 
    wt_exp e2 ty -> 
 (* -------------------------- *)
    wt_exp (ifte b e1 e2) ty. 

(** **** Exercise: Soundness of typing, 3 stars *)

(** Why bother with a type system? To ensure soundness: any well-typed
    expression _must_ successfully evaluate to a value (_progress_) of
    the same type (_preservation_): *)


Require Import Ring.
Require Import Omega.
Lemma wt_exp_sound: 
  forall e ty, 
    wt_exp e ty -> 
    exists v, 
        eval e = ret v
      /\ wt_value v ty.
Proof.
  intros e ty Hexp.

  (**** By induction on e : Stuck at IFTE *
  induction e.
  - simpl. exists v. split.
    + auto.
    + inversion Hexp. auto.
  - inversion Hexp.
    destruct IHe1, IHe2; subst; auto.
    destruct H4, H5. inversion H0. inversion H4.
    subst. simpl. rewrite H, H2. simpl.
    exists (value_nat (n + n0)).
    split.
    + auto.
    + constructor.
  - inversion Hexp.
    destruct IHe1, IHe2, IHe3; auto.
    rewrite <- H3. clear H3.
    Admitted.
   *)

  (**** By induction on Hexp ****)
  
  induction Hexp.
  - inversion H.
    exists (value_bool b). simpl.
    split. reflexivity. constructor.
    exists (value_nat n). simpl.
    split. reflexivity. constructor.
    
  - destruct IHHexp1, IHHexp2; subst; auto.
    clear Hexp1 Hexp2.
    destruct H, H0. inversion H1. inversion H2.
    subst. simpl. rewrite H, H0. simpl.
    exists (value_nat (n + n0)).   
    split.
    + reflexivity.
    + constructor.
  - destruct IHHexp1 as (v1 & Hv1 & Hv1').
    destruct IHHexp2 as (v2 & Hv2 & Hv2').
    destruct IHHexp3 as (v3 & Hv3 & Hv3').
    clear Hexp1 Hexp2 Hexp3.
    simpl.
    rewrite Hv1. clear Hv1.
    rewrite Hv2. clear Hv2.
    rewrite Hv3. clear Hv3.
    simpl.
    inversion Hv1'. clear Hv1'.
    clear H.
    destruct b0.
    + exists v2.
      split.
      * reflexivity.
      * assumption.
    + exists v3.
      split.
      * reflexivity.
      * assumption.
Qed.
  

    (** *** Exercise: Machine code, 1 star *)

(** Similarly, we must define a simply-typed description of machine
    code: *)

Inductive code : Type :=
| skip : code
| seq : code -> code -> code
| PUSH : value -> code
| ADD : code
| IFTE : code -> code -> code.            

Definition stack := list value.

(** **** Exercise: execution of machine code, 3 stars *)

(** As before, the execution must now be partial. You should therefore
    implement *)

Fixpoint exec (c: code)(s: stack): failure stack  :=
  match c with
  | skip => ret s
  | seq c1 c2 => let s1 := exec c1 s in
                 match s1 with
                 | Some s1' => exec c2 s1'
                 | _ => error tt
                 end
  | PUSH v => ret (cons v s)
  | ADD => match s with
           | (value_nat n1) :: s' =>
             match s' with
             | (value_nat n2) :: s'' => ret ((value_nat (n1 + n2)) :: s'')
             | _  => error tt
               end
           | _  => error tt
                         
           end
  | IFTE c1 c2 => match s with
                  | (value_bool b) :: s' => if b then exec c1 s'
                                            else exec c2 s'
                  | _ => error tt
                  end
  end.

(** **** Exercise: Typing of machine code, 4 stars *)

Definition stack_typ := list typ.

(** As for values and expressions, we must cast the typing judgment of
    stacks and machine code as inductive relations. *)

Inductive wt_stack: stack -> stack_typ -> Prop :=
| wt_empty: forall (s: stack) (st: stack_typ),
    
 (* ---------------------------*)
    wt_stack [] []

| wt_cons: forall (v: value) (t: typ) (s: stack) (st: stack_typ),

    wt_value v t ->
    wt_stack s st ->
 (* ---------------------------*)
    wt_stack (v::s) (t:: st)
.



Inductive wt_code: code -> stack_typ -> stack_typ -> Prop :=
| wt_skip: forall st,

    wt_code skip st st

| wt_seq : forall c1 c2 st1 st2 st3,

    wt_code c1 st1 st2 ->
    wt_code c2 st2 st3 ->
    
    wt_code (seq c1 c2) st1 st3

| wt_PUSH: forall v t st,

    wt_value v t ->
    wt_code (PUSH v) st (t::st)

| wt_ADD: forall st,

    wt_code ADD (Nat::Nat::st) (Nat::st)

| wt_IFTE: forall c1 c2 st,
    wt_code (IFTE c1 c2) (Bool::st) st
.

(** then state and prove the soundness of your type system. *)

Lemma wt_code_sound:
    forall c s st st',
    wt_code c st st' ->
    wt_stack s st ->
    exists s',
        exec c s = ret s' 
      /\ wt_stack s' st'.
Proof.
  intros; generalize dependent s. 
  induction H; intros s Hwt_s; simpl; 
    eauto using wt_stack.
  - edestruct IHwt_code1 as (s' & Hexec_s' & Hwt_s'); eauto.
    edestruct IHwt_code2 as (s'' & Hexec_s'' & Hwt_s''); eauto.
    exists s''. rewrite Hexec_s'; simpl. rewrite Hexec_s''; simpl. 
    eauto.
  - destruct s; inversion_clear Hwt_s.
    destruct s; inversion_clear H0.
    destruct v0; inversion_clear H1.
    destruct v; inversion_clear H.
    eauto using wt_cons, wt_value.
  - inversion_clear Hwt_s.
    edestruct IHwt_code1 as (s1 & Hexec_s1 & Hwt_s1); eauto.
    edestruct IHwt_code2 as (s2 & Hexec_s2 & Hwt_s2); eauto.
    destruct v; inversion_clear H1.
    exists (if b then s1 else s2); destruct b; eauto.
Qed.




    (** *** Compilation *)  
      
(** Ignoring types, the compilation function is exactly the same as
    before. In particular, it remains a total function. *)

Fixpoint compile (e: exp): code :=
  match e with
  | val v => PUSH v
  | plus e1 e2 => seq (compile e2) (seq (compile e1) ADD)
  | ifte b e1 e2 => seq (compile b) (IFTE (compile e1) (compile e2))
  end.

(** **** Exercise: Correctness, 5 stars *)

(** Inspired by the earlier correctness statement, state and prove the
correctness of this compiler. 

Hint: you will very likely need to prove the following technical lemma

[[
Lemma bind_split {X Y}: 
  forall (mx: failure X)(k: X -> failure Y) v,
    let! x := mx in k x = ret v -> 
    exists vx,
        mx = ret vx 
      /\ k vx = ret v.
]]
*)

Lemma correctness: (* YOUR CORRECTNESS STATEMENT *) False. Admitted.


End MonsieurCompilateur.

(** ** Conclusion *)

(** We have seen that dependent types can be used for programming too,
    with some caveats. We took this opportunity to present the more
    idiomatic, "Coq"-way of writing such program. Only further
    research and exploration can tell whether the former style can
    scale to achieve the same result as the latter. *)