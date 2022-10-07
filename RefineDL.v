Require Import CoqDL.syntax.state.
Require Import CoqDL.syntax.expressions.
Require Import CoqDL.semantics.dynamic_semantics.

Variable I : interpretation.
Definition refine (a b : Program) : Prop :=
  forall s f : state, dynamic_semantics_program I a s f -> dynamic_semantics_program I b s f.

