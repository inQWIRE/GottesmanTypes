Require Export Types.
Require Export Setoid.
Require Export List.
Require Export Psatz.
        
(* Programs *)

Inductive Unitary1 := H' | S' | T'.
Inductive Unitary2 := CNOT.

(*
(* Can also use sequence and parallel in place of nats, ala QBricks *)
Inductive prog :=
| H' (n : nat)
| S' (n : nat)
| T' (n : nat)
| CNOT (n1 n2 : nat)
| seq (p1 p2 : prog).
*)

Inductive prog :=
| U1 (U : Unitary1) (n : nat)
| U2 (U : Unitary2) (n1 n2 : nat)
| seq (p1 p2 : prog).

Coercion U1 : Unitary1 >-> Funclass.
Coercion U2 : Unitary2 >-> Funclass.
Infix ";" := seq (at level 51, right associativity).

(** Basic Typing judgements *)

Parameter has_type : prog -> GType -> Prop.

Notation "p :: T" := (has_type p T).

Axiom HTypes : H' 0 :: (X → Z) ∩ (Z → X).
Axiom STypes : S' 0 :: (X → Y) ∩ (Z → Z).
Axiom CNOTTypes : CNOT 0 1 :: (X ⊗ I → X ⊗ X) ∩ (I ⊗ X → I ⊗ X) ∩
                             (Z ⊗ I → Z ⊗ I) ∩ (I ⊗ Z → Z ⊗ Z).

(* T only takes Z → Z *)
Axiom TTypes : T' 0 :: (Z → Z).

Axiom SeqTypes : forall g1 g2 A B C,
    g1 :: A → B ->
    g2 :: B → C ->
    g1 ; g2 :: A → C.

Axiom seq_assoc : forall p1 p2 p3 A,
    p1 ; (p2 ; p3) :: A <-> (p1 ; p2) ; p3 :: A.

(* Note that this doesn't restrict # of qubits referenced by p. *)
Axiom TypesI : forall p, p :: I → I.
Axiom TypesI2 : forall p, p :: I ⊗ I → I ⊗ I.
Hint Resolve TypesI TypesI2 : base_types_db.

(** ** Structural rules *)

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
  apply cap_elim in H as [TA TB].
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
    + eapply cap_elim_l. apply H0.
    + apply H0.
    + eapply cap_elim_l. apply H.
  - eapply arrow_sub; intros.
    + eapply cap_elim_r. apply H0.
    + apply H0.
    + eapply cap_elim_r. apply H.
Qed.

(** ** Typing Rules for Tensors *)
(* TODO: Replace with sensible lookup-based rules *)

Axiom tensor_types1 : forall (u : Unitary1) l k A A',
  u 0 :: A → A' ->
  nth_error l k = Some A ->
  u k :: tensor l → tensor (update l k A').

Axiom tensor_types2 : forall (u : Unitary2) l j k A B A' B',
  j <> k ->
  u 0 1 :: A ⊗ B → A' ⊗ B' ->  
  nth_error l j = Some A ->
  nth_error l k = Some B ->
  u j k :: tensor l → tensor (update (update l j A') k B').

(** ** Arrow rules *)

(* Does this need restrictions? 
   If we had g :: X → iX then we could get 
   g :: I → -I which makes negation meaningless 
   (and leads to a contradiction if I ∩ -I = ⊥).    
*)

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

Hint Resolve HTypes STypes TTypes CNOTTypes : base_types_db.
Hint Resolve cap_elim_l cap_elim_r : base_types_db.

Hint Resolve HTypes STypes TTypes CNOTTypes : typing_db.
Hint Resolve cap_intro cap_elim_l cap_elim_r : typing_db.
Hint Resolve SeqTypes : typing_db.

Axiom Geq_types : forall g A A', A == A' -> g :: A -> g :: A'.

Add Parametric Morphism : has_type with signature eq ==> Geq ==> iff as GT_mor.
Proof. intros. split; apply Geq_types; rewrite H; easy. Qed.

Lemma Geq_arrow_l : forall g A A' B,
    g :: A → B ->
    A == A' ->
    g :: A' → B.
Proof. intros. rewrite <- H0; easy. Qed.

Lemma Geq_arrow_r : forall g A B B',
    g :: A → B ->
    B == B' ->
    g :: A → B'.
Proof. intros. rewrite <- H0. easy. Qed.

(* Tactics *)

Ltac is_I A :=
  match A with
  | I => idtac
  end.

Ltac is_prog1 A :=
  match A with
  | H' => idtac
  | S' => idtac
  | T' => idtac
  end. 
              
Ltac is_prog2 A :=
  match A with
  | CNOT => idtac
  end.

Ltac print_goal :=
  match goal with
  |- ?A => idtac A
  end.

Ltac type_check_base :=
  repeat apply cap_intro;
  repeat eapply SeqTypes; (* will automatically unfold compound progs *)
  repeat match goal with
         | |- ?g :: ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- Singleton ?S      => tryif is_evar S then fail else auto 50 with sing_db
         | |- ?g :: ?A → ?B      => tryif is_evar B then fail else eapply Geq_arrow_r
         | |- ?g :: - ?A → ?B    => apply arrow_neg
         | |- ?g :: i ?A → ?B    => apply arrow_i
         | |- U1 ?u _ :: tensor ?A → ?B => eapply tensor_types1; [|easy]
         | |- U2 ?u _ _ :: tensor ?A → ?B =>
           progress (eapply tensor_types2; [lia| |easy|easy])
         | |- ?g :: ?A * ?B → _  => apply arrow_mul
         | |- ?g :: ?A ⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             (* should be able to rewrite directly *)
             eapply Geq_arrow_l; [|rewrite decompose_tensor; reflexivity]
         | |- tensor ?B == tensor ?B' => tryif has_evar B then fail else show_tensor_eq
         | |- ?B == ?B'               => tryif has_evar B then fail else show_mul_eq
         end.  
