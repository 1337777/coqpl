(** remove printing ~ *)
(** printing ~ %\ensuremath{\sim}% *)
(* * Maclane Associative Coherence *)
(* begin hide *)
Require Import CpdtTactics.
Require Import coherence.
Require Import coherence2.
Set Implicit Arguments.
Inductive List := .
(* end hide *)
(** This recursive square [normalize_map_assoc] is the "functorial" parallel to the normalization/flattening of binary trees; and is simply the unit of the reflection for the adjunction.
*)

(* begin hide *)
Infix "/\0" := (up_0) (at level 59, right associativity).
Print objects.
(** %\vspace{-.15in}%  [[
Inductive objects : Set :=
    letter : letters -> objects | /\0 : objects -> objects -> objects.
]]
*)
Infix "~a" := same_assoc (at level 69).
Print same_assoc.
(* end hide *)
(** %\vspace{-.15in}% [[
Inductive same_assoc : forall A B : objects, arrows_assoc A B -> arrows_assoc A B -> Set
 := same_assoc_refl : forall (A B : objects) (f : arrows_assoc A B), f ~a f
 | ...
 | same_assoc_bracket_left_5 : forall A B C D : objects,
   bracket_left_assoc (A /\0 B) C D <oa bracket_left_assoc A B (C /\0 D) ~a
   bracket_left_assoc A B C /\1a unitt_assoc D <oa bracket_left_assoc A (B /\0 C) D <oa
   unitt_assoc A /\1a bracket_left_assoc B C D.
]]
*)
(* begin hide *)
Infix "~s" := same' (at level 69).
About same'.
Print normal.
(* end hide *)
(** %\vspace{-.15in}% [[
Inductive normal : objects -> Set :=
normal_cons1 : forall l : letters, normal (letter l)
| normal_cons2 : forall (A : objects) (l : letters), normal A -> normal (A /\0 letter l).
]]
*)
(* begin hide *)
Print normalize_aux.
(* end hide *)
(** %\vspace{-.15in}% [[
Fixpoint normalize_aux (Z A : objects) {struct A} : objects :=
  match A with
    | letter l => Z /\0 letter l
    | A1 /\0 A2 => (Z </\0 A1) </\0 A2
  end
where "Z </\0 A" := (normalize_aux Z A).
]]
*)
(* begin hide *)
Print normalize.
(* end hide *)
(** %\vspace{-.15in}% [[
Fixpoint normalize (A : objects) : objects :=
  match A with
    | letter l => letter l
    | A1 /\0 A2 => (normalize A1) </\0 A2
  end.
]]
*)
(* begin hide *)
(* begin courtesy cleanup *)
Notation normalize_aux_unitrefl := normalize_aux_arrow.
Notation normalize_unitrefl := normalize_arrow.
(* end courtesy cleanup *)
(* end hide *)
(* begin hide *)
Notation normalize_aux_unitrefl_assoc := normalize_aux_arrow_assoc.
Infix "</\1a" := (normalize_aux_unitrefl_assoc).
Print normalize_aux_arrow_assoc.
(* end hide *)
(** %\vspace{-.15in}% [[
Fixpoint normalize_aux_unitrefl_assoc Y Z (y : arrows_assoc Y Z) A 
 : arrows_assoc (Y /\0 A) (Z </\0 A) :=
  match A with
    | letter l => y /\1a unitt_assoc (letter l)
    | A1 /\0 A2 => ((y </\1a A1) </\1a A2) <oa bracket_left_assoc Y A1 A2
  end
where "y </\1a A" := (normalize_aux_unitrefl_assoc y A).
]]
*)
(* begin hide *)
Notation normalize_unitrefl_assoc := normalize_arrow_assoc.
Print normalize_arrow_assoc.
(* end hide *)
(** %\vspace{-.15in}% [[
Fixpoint normalize_unitrefl_assoc (A : objects) : arrows_assoc A (normalize A) :=
  match A with
    | letter l => unitt_assoc (letter l)
    | A1 /\0 A2 => (normalize_unitrefl_assoc A1) </\1a A2
  end.
]]
*)
Check th151 : forall A : objects, normal A -> normalize A = A.
(** Aborted th270 : for local variable [A] with [normal A],
although there is the propositional equality [th151: normalize A = A], one gets 
that [normalize A] and [A] are not convertible (definitionally/meta equal);
therefore one shall not regard [normalize_unitrefl_assoc A] and [unitt A] as sharing
the same domain-codomain indices of [arrows_assoc]. *)
(* begin hide *)
(* begin explanation *)
Inductive term_unitt_assoc : forall A B : objects, arrows_assoc A B -> Set :=
  term_unitt_assoc_self : forall A : objects,
                            term_unitt_assoc (unitt_assoc A)
| term_unitt_assoc_at_left : forall (A B : objects) (f : arrows_assoc A B),
                               term_unitt_assoc f ->
                               forall A0 : objects,
                                 term_unitt_assoc (f /\1a unitt_assoc A0)
| term_unitt_assoc_at_right : forall (A A0 B0 : objects)
                                     (f : arrows_assoc A0 B0),
                                term_unitt_assoc f ->
                                term_unitt_assoc (unitt_assoc A /\1a f).
Hint Constructors term_unitt_assoc.
Lemma th270_old_corrected : forall A, normal A -> term_unitt_assoc (normalize_unitrefl_assoc A).
  induction 1; crush.
Defined.
(* end explanation *)
(* end hide *)

Check th260 : forall N P : objects, arrows_assoc N P -> normalize N = normalize P.
(** Aborted lemma_coherence_assoc0 : for local variables [N], [P] with [arrows_assoc N P],
although there is the propositional equality [th260 : normalize N = normalize P],
one gets that [normalize N] and [normalize P] are not convertible (definitionally/meta equal);
therefore some transport other than [eq_rect], some coherent transport is lacked. *)

(** Below [directed y] signify that [y] is in the image of the embedding of [arrows] into [arrows_assoc]. *)

(* begin hide *)
Section section_scope.
Open Scope type_scope.
(* end hide *)
Check normalize_aux_map_assoc : forall (X Y : objects) (x : arrows_assoc X Y)
         (Z : objects) (y : arrows_assoc Y Z), directed y ->
       forall (A B : objects) (f : arrows_assoc A B),
       { y_map : arrows_assoc (Y </\0 A) (Z </\0 B) &
       (y_map <oa x </\1a A ~a y </\1a B <oa x /\1a f) * directed y_map }.

Check normalize_map_assoc : forall (A B : objects) (f : arrows_assoc A B),
       { y_map : arrows_assoc (normalize A) (normalize B) &
       (y_map <oa normalize_unitrefl_assoc A ~a
         normalize_unitrefl_assoc B <oa f) * directed y_map }.
(* begin hide *)
Close Scope type_scope.
End section_scope.
(* end hide *)
Print Assumptions normalize_map_assoc.
(** <<
Closed under the global context
>>
*)
(* begin hide *)
Print Assumptions lemma_coherence_assoc.
(**  %\vspace{-.15in}% [[
JMeq.JMeq_eq
Eqdep.Eq_rect_eq.eq_rect_eq
]]
*)
(* end hide *)
