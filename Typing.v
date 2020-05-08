Require Import Types.

(* Programs *)

(* Can also use sequence and parallel in place of nats, ala QBricks *)
Inductive prog :=
| H (n : nat)
| S (n : nat)
| T (n : nat)
| CNOT (n1 n2 : nat)
| seq (p1 p2 : prog).

Infix ";" := seq (at level 60).

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

