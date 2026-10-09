From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.


(* ======== Exercise 1 ======== *)

Inductive form :=
  | FVar		: string -> form
  | FTrue 	: form
  | FFalse  : form
  | FAnd		: form -> form -> form
  | FOr   	: form -> form -> form
  | FImp 		: form -> form -> form
  | FNot   	: form -> form.


(* ======== Exercise 2 ======== *)

Definition x : form := FVar "x".
Definition y : form := FVar "y".
Definition z : form := FVar "z".

Definition T : form := FTrue.
Definition F : form := FFalse.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>"  := e (e custom com_aux) : com_scope.
Notation "e"        := e (in custom com_aux at level 0, e custom com) : com_scope.
Notation "( x )"    := x (in custom com, x at level 99) : com_scope.
Notation "x"        := x (in custom com at level 0, x constr at level 0) : com_scope.

Notation "~ x"      := (FNot x)   (in custom com at level 75, right associativity).
Notation "x /\ y"   := (FAnd x y) (in custom com at level 81, left associativity).
Notation "x \/ y"   := (FOr x y)  (in custom com at level 86, left associativity).
Notation "x -> y"   := (FImp x y) (in custom com at level 99, no associativity).

Open Scope com_scope.

(* Used for debugging *)
(* Set Printing All. *) 

(* (x ∨ ¬y) ∧ (¬x ∨ y) *)
Definition form_1 : form := <{ (x \/ ~y) /\ (~x \/ y) }>.
Print form_1.

(* ¬y → (x ∨ y) *)
Definition form_2 : form := <{ ~y -> (x \/ y) }>.
Print form_2.

(* x ∧ ¬x ∧ ⊤*)
Definition form_3 : form := <{ x /\ ~x /\ T }>.
Print form_3.



(* ======== Exercise 3 ======== *)

Definition valuation := string -> bool.

Fixpoint valid (V : valuation) (p : form) : Prop :=
  match p with
  | FVar x    => V x = true
  | FTrue     => True
  | FFalse    => False
  | FAnd x y  => (valid V x) /\ (valid V y)
  | FOr x y   => (valid V x) \/ (valid V y)
  | FImp x y  => (valid V x) -> (valid V y)
  | FNot x    => ~ (valid V x)
  end.



(* ======== Exercise 4 ======== *)

Definition satisfiable (p : form) : Prop :=
  exists V : valuation, valid V p.

Definition valuation_all_true : valuation := fun _ => true.

Lemma test_form_1 : satisfiable form_1.
Proof.
  intros. unfold satisfiable. exists valuation_all_true. simpl. tauto.
Qed.

Lemma test_form_2 : satisfiable form_2.
Proof.
  intros. unfold satisfiable. exists valuation_all_true. simpl. tauto.
Qed.



(* ======== Exercise 5 ======== *)

Fixpoint find_vars (p : form) : list string :=
  nodup string_dec
    match p with
    | FVar x                        => [x]
    | FTrue | FFalse                => []
    | FAnd x y | FOr x y | FImp x y => find_vars x ++ find_vars y
    | FNot x                        => find_vars x
    end.

Example find_vars_form_1:
  find_vars form_1 = ["x"%string; "y"%string].
Proof. reflexivity. Qed.

Example find_vars_form_3:
  find_vars form_3 = ["x"%string].
Proof. reflexivity. Qed.

Example find_vars_no_vars:
  find_vars <{ T -> F /\ T }> = [].
Proof. reflexivity. Qed.


Fixpoint gen_bool_perms (n : nat) : list (list bool) :=
  match n with
  | 0    => [[]]
  | S n' =>
      let perms := gen_bool_perms n' in
      (map (cons true) perms) ++ (map (cons false) perms)
  end.

Example gen_bool_perms_n_2:
  let perms := gen_bool_perms 2 in
  In [true; true] perms /\
  In [true; false] perms /\
  In [false; true] perms /\
  In [false; false] perms /\
  length perms = 4.
Proof. simpl. tauto. Qed.

Fixpoint lookup (vars : list string) (bool_perm : list bool) (str : string) : bool :=
  match vars, bool_perm with
  | x :: xs, b :: bs => if eqb x str then b else lookup xs bs str
  | _, _ => false
  end.

Definition gen_valuations (vars : list string) (bool_perms : list (list bool)) : list valuation :=
  map (lookup vars) bool_perms.


Fixpoint eval_form (V : valuation) (p : form) : bool :=
  match p with
  | FVar x    => V x
  | FTrue     => true
  | FFalse    => false
  | FAnd x y  => andb (eval_form V x) (eval_form V y)
  | FOr x y   => orb  (eval_form V x) (eval_form V y)
  | FImp x y  => implb (eval_form V x) (eval_form V y)
  | FNot x    => negb (eval_form V x)
  end.

Example eval_form_1:
  eval_form valuation_all_true form_1 = true.
Proof. reflexivity. Qed.

Example eval_form_2:
  eval_form valuation_all_true form_2 = true.
Proof. reflexivity. Qed.

Example eval_form_3:
  eval_form valuation_all_true form_3 = false.
Proof. reflexivity. Qed.


Definition find_valuation (p : form) : option valuation :=
  let vars       := find_vars p in
  let bool_perms := gen_bool_perms (length vars) in
  find (fun x => eval_form x p) (gen_valuations vars bool_perms).



(* ======== Exercise 6 ======== *)

Definition solver (p : form) : bool :=
  match find_valuation p with
  | Some _ => true
  | None   => false
  end.

(** The difference between satisfiable and solver is that 
		satisfiable is a logical definition in Coq’s Prop world.
		It states that there exists a valuation (assignment of truth values)
		that makes a formula true, and it’s used for proofs rather than computation. 
		
		In contrast, solver is a computational function returning a bool that actually
		tries to find such a valuation by enumerating and evaluating all possibilities. 
		
		Thus, satisfiable expresses the theoretical property of satisfiability, while 
		solver provides a practical algorithm to test it.
*)


(* ======== Exercise 7 ======== *)

Example test_solver_pos_1:
  solver <{ (~x) /\ (y \/ z) }> = true.
Proof. reflexivity. Qed.

Example test_solver_pos_2:
  solver <{ x \/ (~x) }> = true.
Proof. reflexivity. Qed.

Example test_solver_pos_3:
  solver <{ T \/ (~T) }> = true.
Proof. reflexivity. Qed.

Example test_solver_neg_1:
  solver <{ ~x /\ x }> = false.
Proof. reflexivity. Qed.

Example test_solver_neg_2:
  solver <{ T -> F /\ T }> = false.
Proof. reflexivity. Qed.



(* ======== Exercise 8 ======== *)

Lemma eval_form_valid :
  forall V p, eval_form V p = true <-> valid V p.
Proof.
  intros V p.
  induction p; simpl.
  (* FVar *) 
  - destruct (V s). tauto. split; auto.
  (* FTrue *) 
  - tauto.
  (* FFalse *)
  - split; auto. discriminate.
  (* FAnd *)
  - split; intros; rewrite andb_true_iff in *; tauto.
  (* FOr *)
  - split; intros; rewrite orb_true_iff in *; tauto.
  (* FImp *)
  - split; intros; rewrite implb_true_iff in *; tauto.
  (* FNot *)
  - split; unfold not; intros.
    + rewrite negb_true_iff in H. apply IHp in H0. rewrite H in H0. discriminate.
    + rewrite negb_true_iff. destruct (eval_form V p); tauto.
Qed.


Theorem solver_sound p :
  solver p = true -> satisfiable p.
Proof.
  intros H.
  unfold solver, satisfiable in *.
  destruct (find_valuation p) as [v|] eqn:Heq.
  - clear H. exists v.
    unfold find_valuation in Heq.
    induction (gen_valuations (find_vars p) (gen_bool_perms (length (find_vars p)))) as [|v' vs IH].
    + discriminate.
    + destruct (eval_form v' p) eqn:Ha.
      * inversion Heq. apply eval_form_valid. rewrite Ha in H0. inversion H0. subst. assumption.
      * inversion Heq. rewrite Ha in H0. apply IH; eauto.
  - discriminate.
Qed.



(* ======== Exercise 9 : Extension 1 ======== *)

Fixpoint optimizer (p : form) : form :=
  match p with
  | FAnd x y => match x, y with
    | FTrue,  y      => optimizer y
    | x,      FTrue  => optimizer x
    | FFalse, _      => FFalse
    | _,      FFalse => FFalse
    | x, y           => FAnd (optimizer x) (optimizer y)
    end
	| FOr x y => match x, y with
		| FTrue,  _      => FTrue
    | _,      FTrue  => FTrue
    | FFalse, y      => optimizer y
    | x,      FFalse => optimizer x
    | x, y           => FOr (optimizer x) (optimizer y)
    end
  | FImp x y           => FImp (optimizer x) (optimizer y)
  | FNot x             => FNot (optimizer x)
  | p'                 => p'
  end.

Lemma optimizer_eval_form : 
	forall V p, eval_form V p = eval_form V (optimizer p).
Proof.
  intros. induction p; try (simpl; congruence).
	(* FAnd *)
  - simpl. destruct p1, p2;
      try (rewrite IHp1; rewrite IHp2);
      try apply andb_true_r;
      try apply andb_false_r;
      reflexivity.
	(* FOr *)
  - destruct p1, p2; simpl in *;
      try rewrite <- IHp1;
      try rewrite <- IHp2;
      try apply orb_true_r;
      try apply orb_false_r;
      reflexivity.
Qed.

Theorem optimizer_valid : 
	forall V p, valid V p <-> valid V (optimizer p).
Proof.
  split; intros;
  apply eval_form_valid;
  apply eval_form_valid in H;
  try rewrite <- optimizer_eval_form;
  try rewrite <- optimizer_eval_form in H;
  congruence.
Qed.

Theorem optimizer_satisfiable : 
	forall p, satisfiable p <-> satisfiable (optimizer p).
Proof.
  unfold satisfiable.
  split; intros [V H]; exists V;
  [apply optimizer_valid in H | apply optimizer_valid]; congruence.
Qed.



(* ======== Exercise 9 : Extension 2 ======== *)

Fixpoint nnf_converter (p : form) : form :=
  match p with
  | FAnd x y  => FAnd (nnf_converter x) (nnf_converter y)
  | FOr  x y  => FOr  (nnf_converter x) (nnf_converter y)
  | FImp x y  => FOr  (nnf_negator x)   (nnf_converter y)
  | FNot x    => nnf_negator x
  | p'        => p'
  end

with nnf_negator (p : form) : form :=
  match p with
  | FVar x    => FNot (FVar x)
  | FTrue     => FFalse
  | FFalse    => FTrue
  | FAnd x y  => FOr  (nnf_negator x) (nnf_negator y)
  | FOr  x y  => FAnd (nnf_negator x) (nnf_negator y)
  | FImp x y  => FAnd (nnf_converter x) (nnf_negator y)
  | FNot x    => nnf_converter x
  end.

Lemma negb_nnf_negator : 
	forall V p,
  negb (eval_form V (nnf_converter p)) = eval_form V (nnf_negator p) /\
  negb (eval_form V (nnf_negator p))   = eval_form V (nnf_converter p).
Proof.
  intros. induction p; split; simpl;
  try rewrite negb_involutive;
  try destruct IHp as [IHp1 IHp2]; auto;
  destruct IHp1 as [IHnc1 IHnn1];
  destruct IHp2 as [IHnc2 IHnn2];
  try rewrite negb_andb;
  try rewrite negb_orb;
  try rewrite IHnc1;
  try rewrite IHnc2;
  try rewrite IHnn1;
  try rewrite IHnn2;
  reflexivity.
Qed.

Theorem nnf_converter_eval_form : 
	forall V p, eval_form V p = eval_form V (nnf_converter p).
Proof.
  intros. induction p; simpl;
  try rewrite IHp1, IHp2; try reflexivity.
  - rewrite implb_orb. destruct (negb_nnf_negator V p1) as [Hnc _].
    rewrite Hnc. reflexivity.
  - destruct (negb_nnf_negator V p) as [Hnc _]. rewrite <- Hnc.
    f_equal. congruence.
Qed.

Definition nnf_solver (p : form) : bool :=
  match find_valuation (nnf_converter p) with
  | Some _ => true
  | None   => false
  end.

Lemma nnf_solver_eq p :
  nnf_solver p = solver (nnf_converter p).
Proof. reflexivity. Qed.

Theorem nnf_solver_sound p :
  nnf_solver p = true -> satisfiable p.
Proof.
  rewrite nnf_solver_eq. intros.
  apply solver_sound in H.
  unfold satisfiable in *.
  destruct H as [v H]. exists v.
  apply eval_form_valid. apply eval_form_valid in H.
  rewrite nnf_converter_eval_form. assumption.
Qed.
