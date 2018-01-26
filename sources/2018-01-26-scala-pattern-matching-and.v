
From Coq Require Import String List.

Inductive scala_case_condition : Set -> Set -> Type :=
  | case_pred    : forall A : Set,   (A -> bool)     -> scala_case_condition A A
  | case_extract : forall A B : Set, (A -> option B) -> scala_case_condition A (A * B).

Inductive scala_case : Set -> Set -> Type :=
  | case : forall A B C : Set, scala_case_condition A B -> (B -> C) -> scala_case A C.

Inductive scala_match (A B : Set) : Type :=
  | match_constr : list (scala_case A B) -> scala_match A B.

(* marking type parameters implicit *)

Arguments case_pred [A].
Arguments case_extract [A B].
Arguments case [A B C].
Arguments match_constr [A B].

(* how to evaluate scala_match *)

Definition eval_case_condition : forall (A B : Set), A -> scala_case_condition A B -> option B.
  intros A B a cond.
  inversion cond as [ A0 p | A0 C e ].
  - subst A0 B. exact (if p a then Some a else None).
  - subst A0.   exact (option_map (fun c => (a, c)) (e a)).
Defined.

Arguments eval_case_condition [A B].

Definition eval_case : forall (A B : Set), A -> scala_case A B -> option B.
  intros A B a case.
  inversion case as [ A0 C B0 cond f ]. subst A0 B0.
  exact (option_map f (eval_case_condition a cond)).
Defined.

Arguments eval_case [A B].

Definition eval_match (A B : Set) (a : A) (m : scala_match A B) : option B :=
  match m with
  | match_constr cases =>
      (fix loop cs :=
          match cs with
          | nil      => None
          | cons h t =>
              match eval_case a h with
              | Some b => Some b
              | None   => loop t
              end
          end) cases
  end.

Arguments eval_match [A B].

(* simple match example *)

Record user : Set := mkUser {
    username     : string;
    emailAddress : string
  }.

Definition username_extractor (u : user) : option string := Some (username u).
Definition tru (u : user) : bool := true.
Definition fls (u : user) : bool := false.

Open Scope string_scope.

Eval compute in (
  eval_match (mkUser "username" "") 
    (match_constr  (
      case (case_pred fls) (fun _ => "fls") ::
      case (case_extract username_extractor) snd ::
      case (case_pred tru) (fun _ => "tru") ::
      nil)
    )
).

(* defining the pattern matching combinator *)

Definition and_match : forall A B X Y : Set,
    scala_case_condition A X -> scala_case_condition A Y -> (X -> Y -> B) -> scala_case A B.
  intros A B X Y c1 c2 f.
  inversion c1 as [ A0 p1 | A0 C1 e1 ]; subst A0 X;
  inversion c2 as [ A0 p2 | A0 C2 e2 ]; subst A0 Y.
  - exact (case (case_pred (fun a => andb (p1 a) (p2 a))) (fun a => f a a)).
  - exact (case (case_extract
            (fun a => match (p1 a), (e2 a) with
                      | true, Some c => Some c
                      | _   , _      => None
                      end))
            (fun ac => f (fst ac) ac)).
  - exact (case (case_extract
            (fun a => match (e1 a), (p2 a) with
                      | Some c, true => Some c
                      | _     , _    => None
                      end))
            (fun ac => f ac (fst ac))).
  - exact (case (case_extract
            (fun a => match (e1 a), (e2 a) with
                      | Some c1, Some c2 => Some (c1, c2)
                      | _      , _       => None
                      end))
            (fun acc => f (fst acc, fst (snd acc)) (fst acc, snd (snd acc)) )).
Defined.

Arguments and_match [A B X Y].

(* some properties *)

Definition cond_matches (A B : Set) (a : A) (cond : scala_case_condition A B) : Prop :=
  exists x, eval_case_condition a cond = Some x.

Definition case_matches (A B : Set) (a : A) (case : scala_case A B) : Prop :=
  exists x, eval_case a case = Some x.

Arguments cond_matches [A B].
Arguments case_matches [A B].

Lemma if_both_branches : forall (A : Type) (b : bool) (a : A), (if b then a else a) = a.
Proof.
  intros A b a. case b.
  - reflexivity.
  - reflexivity.
Qed.

Lemma match_option_both_branches : forall (A B : Type) (a : option A) (b : B),
    (match a with | Some _ => b | None => b end) = b.
Proof.
  intros A B a b. case a.
  - reflexivity.
  - reflexivity.
Qed.

Ltac simpl_eq_rec := simpl; unfold eq_rec_r; simpl.
Ltac simpl_eq_rect := simpl; unfold eq_rect_r; simpl; unfold eq_rec_r; simpl.

Ltac solve_for_pred p a H :=
  exists a; simpl_eq_rec; generalize H; simpl_eq_rect; unfold option_map; case (p a);
  try rewrite Bool.andb_false_r; try rewrite match_option_both_branches; easy.

Ltac solve_for_extract o a H :=
  generalize H; unfold cond_matches; simpl_eq_rect; case (o a);
  [ intros x1 H1; exists (a, x1); now simpl
  | unfold option_map; simpl; try
      (now rewrite if_both_branches || now rewrite match_option_both_branches || discriminate) ].

Theorem and_match_both_match_1 : forall (A B X Y : Set) (a : A) (f : X -> Y -> B)
    (c1 : scala_case_condition A X) (c2 : scala_case_condition A Y),
    case_matches a (and_match c1 c2 f) -> cond_matches a c1 /\ cond_matches a c2.
Proof.
  intros A B X Y a f.
  induction c1 as [ A p1 | A C1 e1 ]; induction c2 as [ A p2 | A C2 e2 ].
  - intros [x H]. split.
    + solve_for_pred    p1 a H.
    + solve_for_pred    p2 a H.
  - intros [x H]. split.
    + solve_for_pred    p1 a H.
    + solve_for_extract e2 a H.
  - intros [x H]. split.
    + solve_for_extract e1 a H.
    + solve_for_pred    p2 a H.
  - intros [x H]. split.
    + solve_for_extract e1 a H.
    + solve_for_extract e2 a H.
Qed.

Ltac subst_over_some :=
  intros; repeat (
    match goal with
    | HSome: Some _ = Some _ |- _ => injection HSome; clear HSome
    end; intros; subst
  ).

Ltac solve_for_case p1 p2 a f :=
  intros [[x1 H1] [x2 H2]]; generalize H1 H2; unfold case_matches; simpl_eq_rect;
  intros H3 H4; exists (f x1 x2); generalize H3 H4;
  case (p1 a); case (p2 a); try unfold option_map; subst_over_some; now simpl.

Theorem and_match_both_match_2 : forall (A B X Y : Set) (a : A) (f : X -> Y -> B)
    (c1 : scala_case_condition A X) (c2 : scala_case_condition A Y),
    cond_matches a c1 /\ cond_matches a c2 -> case_matches a (and_match c1 c2 f).
Proof.
  intros A B X Y a f.
  induction c1 as [ A p1 | A C1 e1 ]; induction c2 as [ A p2 | A C2 e2 ].
  - solve_for_case p1 p2 a f.
  - solve_for_case p1 e2 a f.
  - solve_for_case e1 p2 a f.
  - solve_for_case e1 e2 a f.
Qed.

Theorem and_match_both_match : forall (A B X Y : Set) (a : A) (f : X -> Y -> B)
    (c1 : scala_case_condition A X) (c2 : scala_case_condition A Y),
    case_matches a (and_match c1 c2 f) <-> cond_matches a c1 /\ cond_matches a c2.
Proof.
  split; [ apply and_match_both_match_1 | apply and_match_both_match_2 ].
Qed.

