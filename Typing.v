Require Export Types.

(* Programs *)

(* Can also use sequence and parallel in place of nats, ala QBricks *)
Inductive prog :=
| H (n : nat)
| S (n : nat)
| T (n : nat)
| CNOT (n1 n2 : nat)
| seq (p1 p2 : prog).

Infix ";" := seq (at level 51, right associativity).

(* I, X, Y and Z as derived gates *)
Definition Z' n : prog := S n ; S n.
Definition X' n : prog := H n ; Z' n; H n.
Definition Y' n : prog := S n; X' n; Z' n; S n.
Definition I' n : prog := H n; H n.

(* Other common gates *)
Definition CZ m n : prog := H n ; CNOT m n ; H n.
Definition SWAP m n : prog := CNOT m n; CNOT n m; CNOT m n.


(** Basic Typing judgements *)

Parameter has_type : prog -> GType -> Prop.

Notation "H :: T" := (has_type H T).

Axiom HTypes : H 0 :: (X → Z) ∩ (Z → X).
Axiom STypes : S 0 :: (X → Y) ∩ (Z → Z).
Axiom CNOTTypes : CNOT 0 1 :: (X ⊗ I → X ⊗ X) ∩ (I ⊗ X → I ⊗ X) ∩
                             (Z ⊗ I → Z ⊗ I) ∩ (I ⊗ Z → Z ⊗ Z).

Axiom SeqTypes : forall g1 g2 A B C,
    g1 :: A → B ->
    g2 :: B → C ->
    g1 ; g2 :: A → C.

(* Note that this doesn't restrict # of qubits. *)
Axiom TypesI : forall p, p :: I → I.

(** Structural rules *)

(* Subtyping rules *)
Axiom cap_elim_l : forall g A B, g :: A ∩ B -> g :: A.
Axiom cap_elim_r : forall g A B, g :: A ∩ B -> g :: B.
Axiom cap_intro : forall g A B, g :: A -> g :: B -> g :: A ∩ B.
Axiom cap_arrow : forall g A B C,
  g :: (A → B) ∩ (A → C) ->    
  g :: A → (B ∩ C).

Axiom arrow_sub : forall g A A' B B',
  (forall l, l :: A' -> l :: A) ->
  (forall r, r :: B -> r :: B') ->
  g :: A → B ->
  g :: A' → B'.

Hint Resolve cap_elim_l cap_elim_r cap_intro cap_arrow arrow_sub : subtype_db.

Lemma cap_elim : forall g A B, g :: A ∩ B -> g :: A /\ g :: B.
Proof. eauto with subtype_db. Qed.

Lemma cap_arrow_distributes : forall g A A' B B',
  g :: (A → A') ∩ (B → B') ->
  g :: (A ∩ B) → (A' ∩ B').
Proof.
  intros; apply cap_arrow.  
  apply cap_intro; eauto with subtype_db.
Qed.  

Lemma cap_arrow_distributes' : forall g A A' B B',
  g :: (A → A') ∩ (B → B') ->
  g :: (A ∩ B) → (A' ∩ B').
intros.
  apply cap_elim in H0 as [TA TB].
  apply cap_arrow.
  apply cap_intro.
  - apply arrow_sub with (A := A) (B := A'); trivial. intros l. apply cap_elim_l.
  - apply arrow_sub with (A := B) (B := B'); trivial. intros l. apply cap_elim_r.
Qed.

(* Full explicit proof *)
Lemma cap_arrow_distributes'' : forall g A A' B B',
  g :: (A → A') ∩ (B → B') ->
  g :: (A ∩ B) → (A' ∩ B').
Proof.
  intros.
  apply cap_arrow.
  apply cap_intro.
  - eapply arrow_sub; intros.
    + eapply cap_elim_l. apply H1.
    + apply H1.
    + eapply cap_elim_l. apply H0.
  - eapply arrow_sub; intros.
    + eapply cap_elim_r. apply H1.
    + apply H1.
    + eapply cap_elim_r. apply H0.
Qed.

(** Tensor rules *)

Notation s := Datatypes.S.

Parameter Singleton : GType -> Prop.
Axiom SI: Singleton I.
Axiom SX : Singleton X. 
Axiom SZ : Singleton Z. 
Axiom S_neg : forall A, Singleton A -> Singleton (neg A).
Axiom S_i : forall A, Singleton A -> Singleton (i A).
Axiom S_mul : forall A B, Singleton A -> Singleton B -> Singleton (A * B).

Axiom tensor_inc : forall g n E A A',
    Singleton A ->
    g n :: (A → A') ->
    g (s n) ::  E ⊗ A → E ⊗ A'. 

Axiom tensor_inc2 : forall (g : nat -> nat -> prog) m n E A A' B B',
    Singleton A ->
    Singleton B ->
    g m n :: (A ⊗ B → A' ⊗ B') ->
    g (s m) (s n) ::  E ⊗ A ⊗ B → E ⊗ A' ⊗ B'. 

Axiom tensor_inc2_r : forall (g : nat -> nat -> prog) m n E A A' B B',
    Singleton A ->
    Singleton B ->
    g m n :: (A ⊗ B → A' ⊗ B') ->
    g m (s n) ::  A ⊗ E ⊗ B → A' ⊗ E ⊗ B'. 

(* For flipping CNOTs. Could have CNOT specific rule. *)
Axiom tensor2_comm : forall (g : nat -> nat -> prog) m n  A A' B B',
    Singleton A ->
    Singleton B ->
    g m n :: A ⊗ B → A' ⊗ B' ->
    g n m :: B ⊗ A → B' ⊗ A'.

(** Arrow rules *)

Axiom arrow_mul : forall p A A' B B',
    p :: A → A' ->
    p :: B → B' ->
    p :: A * B → A' * B'.

Axiom arrow_i : forall p A A',
    p :: A → A' ->
    p :: i A → i A'.

Axiom arrow_neg : forall p A A',
    p :: A → A' ->
    p :: -A → -A'.  
  
Axiom arrow_comp : forall p1 p2 A A' A'',
    p1 :: A → A' ->
    p2 :: A' → A'' ->
    p1 ; p2 :: A → A''.

Axiom seq_assoc : forall p1 p2 p3 A,
    p1 ; (p2 ; p3) :: A <-> (p1 ; p2) ; p3 :: A.

Hint Resolve HTypes STypes CNOTTypes : base_types_db.
Hint Resolve cap_elim_l cap_elim_r : base_types_db.

Hint Resolve HTypes STypes CNOTTypes : typing_db.
Hint Resolve cap_intro cap_elim_l cap_elim_r : typing_db.
Hint Resolve arrow_comp : typing_db.

Lemma ZTypes : Z' 0 :: (X → -X) ∩ (Z → Z).
Proof.
  unfold Z'.
  repeat apply cap_intro.  
  - repeat eapply arrow_comp.
    + eauto with base_types_db.
    + eauto with base_types_db.
  apply cap_intro.  
  eapply arrow_comp.
  
  
Lemma XTypes : X' 0 :: (X → X) ∩ (Z → -Z).
Proof.
  unfold X'.
  
  specialize HTypes as H1.
  apply cap_intro.
  - 
