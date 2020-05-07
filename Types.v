(** Types *)

Inductive BasisType := X | Z.

Inductive xzBaseType := I | XZ | B (b : BasisType).

Coercion B : BasisType >-> xzBaseType.

Inductive iBaseType :=
| r : xzBaseType -> iBaseType
| i : xzBaseType -> iBaseType.

Coercion r : xzBaseType >-> iBaseType.

Inductive BaseType :=
| pos : iBaseType -> BaseType
| neg : iBaseType -> BaseType.

Coercion pos : iBaseType >-> BaseType.
Notation "- T" := (neg T).

Inductive tensorType :=
| single : BaseType -> tensorType
| cons   : BaseType -> tensorType -> tensorType.

Coercion single : BaseType >-> tensorType.

Inductive GType :=
| G : tensorType -> GType
| arrow : GType -> GType -> GType
| cap : GType -> GType -> GType.

Coercion G : tensorType >-> GType.

Infix "⊗" := cons (at level 51, right associativity).
Infix "→" := arrow (at level 60, no associativity). 
Infix "∩" := cap (at level 60, no associativity).

(** Multiplying Base Types *)

Definition negate (t : BaseType) : BaseType :=
  match t with
  | pos t' => neg t'
  | neg t' => pos t'
  end.

Definition mul_i (t : BaseType) : BaseType :=
  match t with
  | pos (r t') => i t'
  | pos (i t') => -t'
  | neg (r t') => -(i t')
  | neg (i t') => t'                     
  end.

(* Currently not used 
Definition lift_to_base (f : iBaseType -> iBaseType -> BaseType) :
  BaseType -> BaseType -> BaseType :=
  fun t1 t2 => match t1, t2 with
            | pos t1', pos t2' => f t1' t2'
            | pos t1', neg t2' => negate (f t1' t2')
            | neg t1', pos t2' => negate (f t1' t2')
            | neg t1', neg t2' => f t1' t2'
            end.

Definition lift_to_ibase (f : xzBaseType -> xzBaseType -> iBaseType) :
  iBaseType -> iBaseType -> BaseType :=
  fun t1 t2 => match t1, t2 with
            | r t1', r t2' => f t1' t2'
            | r t1', i t2' => mul_i (f t1' t2')
            | i t1', r t2' => mul_i (f t1' t2')
            | i t1', i t2' => negate (f t1' t2')
            end.
 *)

Definition lift_from_ibase (f : iBaseType -> iBaseType -> BaseType) :
  BaseType -> BaseType -> BaseType :=
  fun t1 t2 => match t1, t2 with
            | pos t1', pos t2' => f t1' t2'
            | pos t1', neg t2' => negate (f t1' t2')
            | neg t1', pos t2' => negate (f t1' t2')
            | neg t1', neg t2' => f t1' t2'
            end.

Definition lift_from_xzbase (f : xzBaseType -> xzBaseType -> BaseType) :
  iBaseType -> iBaseType -> BaseType :=
  fun t1 t2 => match t1, t2 with
            | r t1', r t2' => f t1' t2'
            | r t1', i t2' => mul_i (f t1' t2')
            | i t1', r t2' => mul_i (f t1' t2')
            | i t1', i t2' => negate (f t1' t2')
            end.


Definition bmul (t1 t2 : BasisType) : BaseType :=
  match t1, t2 with
  | X, X => I
  | X, Z => XZ
  | Z, X => -XZ            
  | Z, Z => I
  end.

Definition xzmul (t1 t2 : xzBaseType) : BaseType :=
  match t1, t2 with
  | B b1, B b2 => bmul b1 b2  
  | I, _       => t2
  | _, I       => t1
  | XZ, X      => -Z
  | XZ, Z      => X
  | X,  XZ     => Z
  | Z,  XZ     => -X
  | XZ, XZ     => -I
  end.

Definition imul  (t1 t2 : iBaseType) : BaseType := (lift_from_xzbase xzmul) t1 t2.

Definition gmul (t1 t2 : BaseType) : BaseType := (lift_from_ibase imul) t1 t2.

Infix "*" := gmul.

Notation Y := (i XZ).

Example Xsqr : X * X = I. Proof. reflexivity. Qed.
Example Zsqr : Z * Z = I. Proof. reflexivity. Qed.
Example Ysqr : Y * Y = I. Proof. reflexivity. Qed.
Example XtimesZ : X * Z = XZ. Proof. reflexivity. Qed.
Example ZtimesX : Z * X = -XZ. Proof. reflexivity. Qed.
Example XtimesY : X * Y = i Z. Proof. reflexivity. Qed.
Example YtimesX : Y * X = -i Z. Proof. reflexivity. Qed.
Example ZtimesY : Z * Y = -i X. Proof. reflexivity. Qed.
Example YtimesZ : Y * Z = i X. Proof. reflexivity. Qed.


