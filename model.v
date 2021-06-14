Require Import List.
Import ListNotations.

Inductive pawn : Type := I | O | U.

Inductive position : Type := A1 | B1 | C1 | A2 | B2 | C2 | A3 | B3 | C3.

Definition row : Type := (pawn * pawn * pawn)%type.

Definition game : Type := (row * row * row)%type.

Definition game_start : game := (
  (U, U, U),
  (U, U, U),
  (U, U, U)
  ).

Definition inv ( p : pawn) : pawn :=
  match p with
  | U => U
  | I => O
  | O => I
  end.

Definition diagI (board : game) : bool :=
  match board with
  | ((I, _, _), (_, I, _), (_, _, I)) => true
  | ((_, _, I), (_, I, _), (I, _, _)) => true
  | _ => false
  end.

Definition diagO (board : game) : bool :=
  match board with
  | ((O, _, _), (_, O, _), (_, _, O)) => true
  | ((_, _, O), (_, O, _), (O, _, _)) => true
  | _ => false
  end.

Definition colI (board : game) : bool :=
  match board with
  | ((I, _, _), (I, _, _), (I, _, _)) => true
  | ((_, I, _), (_, I, _), (_, I, _)) => true
  | ((_, _, I), (_, _, I), (_, _, I)) => true
  | _ => false
  end.

Definition colO (board : game) : bool :=
  match board with
  | ((O, _, _), (O, _, _), (O, _, _)) => true
  | ((_, O, _), (_, O, _), (_, O, _)) => true
  | ((_, _, O), (_, _, O), (_, _, O)) => true
  | _ => false
  end.

Definition rowI (board : game) : bool :=
  match board with
  | ((I, I, I), (_, _, _), (_, _, _)) => true
  | ((_, _, _), (I, I, I), (_, _, _)) => true
  | ((_, _, _), (_, _, _), (I, I, I)) => true
  | _ => false
  end.

Definition rowO (board : game) : bool :=
  match board with
  | ((O, O, O), (_, _, _), (_, _, _)) => true
  | ((_, _, _), (O, O, O), (_, _, _)) => true
  | ((_, _, _), (_, _, _), (O, O, O)) => true
  | _ => false
  end.

Definition get (pos : position) (board : game) : pawn :=
  match pos, board with
  | A1, ((x, _, _), _, _) => x
  | B1, ((_, x, _), _, _) => x
  | C1, ((_, _, x), _, _) => x
  | A2, (_, (x, _, _), _) => x
  | B2, (_, (_, x, _), _) => x
  | C2, (_, (_, _, x), _) => x
  | A3, (_, _, (x, _, _)) => x
  | B3, (_, _, (_, x, _)) => x
  | C3, (_, _, (_, _, x)) => x
  end.

Definition set (pos : position) (board : game) (p : pawn) : game :=
  match pos, board with
  | A1, ((_, x, y), r2, r3) => ((p, x, y), r2, r3)
  | B1, ((x, _, y), r2, r3) => ((x, p, y), r2, r3)
  | C1, ((x, y, _), r2, r3) => ((x, y, p), r2, r3)
  | A2, (r1, (_, x, y), r3) => (r1, (p, x, y), r3)
  | B2, (r1, (x, _, y), r3) => (r1, (x, p, y), r3)
  | C2, (r1, (x, y, _), r3) => (r1, (x, y, p), r3)
  | A3, (r1, r2, (_, x, y)) => (r1, r2, (p, x, y))
  | B3, (r1, r2, (x, _, y)) => (r1, r2, (x, p, y))
  | C3, (r1, r2, (x, y, _)) => (r1, r2, (x, y, p))
  end.

Definition pawn_eq (p q : pawn) : bool :=
  match p, q with
  | I, I => true
  | U, U => true
  | O, O => true
  | _, _ => false
  end.

Lemma pawn_eq_eq (p q : pawn):
  p = q <-> pawn_eq p q = true.
Proof.
  split.
  - induction 1, p; reflexivity.
  - induction p, q; simpl; auto; discriminate.
Qed.

Definition row_eq (r1 r2 : row) : bool :=
  match r1, r2 with
  | (a, b, c), (d, e, f) =>
    pawn_eq a d &&
    pawn_eq b e &&
    pawn_eq c f
  end.

Definition game_eq (g1 g2 : game) : bool :=
  match g1, g2 with
  | (a, b, c), (d, e, f) =>
    row_eq a d &&
    row_eq b e &&
    row_eq c f
  end.


Definition free (pos : position) (board : game) : bool :=
  pawn_eq (get pos board) U.

Definition state : Type := (game * pawn)%type.

Definition winI (board : game) : bool :=
  diagI board || rowI board || colI board.

Definition winO (board : game) : bool :=
  diagO board || rowO board || colO board.

Definition game_done (board : game) : bool :=
  winI board || winO board.

Inductive step : state -> state -> Prop :=
  | play_free : forall pos p board,
    free pos board = true ->
    game_done board = false ->
    step (board, p) (set pos board p, inv p).

Notation "s1 --> s2" := (step s1 s2) (at level 80).

Inductive steps : state -> state -> Prop :=
  | steps_one : forall g1 g2,
    step g1 g2 -> steps g1 g2
  | steps_trans : forall g1 g2 g3,
    step g1 g2 -> steps g2 g3 -> steps g1 g3.

Notation "g1 -->> g2" := (steps g1 g2) (at level 80).

Definition On_going (board : game) :=
  game_done board = false.

Definition Done (board : game) :=
  game_done board = true.

Lemma On_going_start :
  On_going game_start.
Proof. reflexivity. Qed.

Ltac play pos :=
  match goal with
    | [ |- steps _ _ ] => eapply steps_trans; [ play pos | idtac; cbn ]
    | [ |- step _ _ ] => apply (play_free pos _ _); auto
  end.

Ltac win pos :=
  match goal with
    | [ |- steps _ _ ] => apply steps_one; win pos
    | [ |- step _ _ ] => apply (play_free pos); auto
  end.

Example game_win_O :
  exists s, (game_start, O) -->> (s, I) /\ winO s = true.
Proof.
  eexists. split.
  - play A1.
    play A2.
    play B1.
    play B2.
    win C1.
  - reflexivity.
Qed.

Definition step_by (g1 : state) (p : position) (g2 : state) : Prop :=
  step g1 g2 /\ fst g2 = set p (fst g1) (snd g1).

Notation "g1 '-<' p '>->' g2" := (step_by g1 p g2) (at level 80).

Inductive steps_by :  state -> list position -> state -> Prop :=
  | seq_one : forall g1 g2 p,
    g1 -<p>-> g2 ->
    steps_by g1 [p] g2
  | seq_cons : forall g1 g2 g3 pos seq,
    steps_by g2 seq g3 ->
    g1 -<pos>-> g2 ->
    steps_by g1 (pos::seq) g3.

Notation "g1 '-<' p '>->>' g2" := (steps_by g1 p g2) (at level 80).


Lemma steps_by_steps :
  forall seq g1 g2,
  g1 -<seq>->> g2 -> g1 -->> g2.
Proof.
  induction 1 as [ g1 g2 p [H _] | g1 g2 g3 p seq H1 H2 [H3 _]].
  - apply (steps_one _ _ H).
  - apply (steps_trans _ _ _ H3).
    apply H2.
Qed.

Lemma step_step_by :
  forall g1 g2,
  g1 --> g2 -> exists pos, g1 -<pos>-> g2.
Proof.
  intros [g1 p1] [g2 p2] [ pos p board H1 H2 ].
  exists pos; split.
  - apply (play_free _ _ _ H1 H2).
  - reflexivity.
Qed.

Lemma steps_steps_by :
  forall g1 g2,
  g1 -->> g2 -> exists seq, g1 -<seq>->> g2.
Proof.
  induction 1 as [ ? ? [ pos ] | g1 g2 g3 H1 H2 (seq & IH)].
  - exists [pos].
    apply seq_one; split; auto using step.
  - apply step_step_by in H1 as (pos & H).
    exists (pos::seq).
    apply (seq_cons _ _ _ _ _ IH H).
Qed.

Fixpoint interleave {A} (l1 l2 : list A) : list A :=
  match l1, l2 with
  | [], [] => []
  | x::xs, [] => [x]
  | [], y::ys => [y]
  | x::xs, y::ys => x::y::interleave xs ys
  end.

Definition count_row (p : pawn) (r : row) :=
  match r with
  | (a, b, c) =>
      (if pawn_eq p a then 1 else 0)
    + (if pawn_eq p b then 1 else 0)
    + (if pawn_eq p c then 1 else 0)
  end.

Definition count_pawn (p : pawn) (g : game) :=
  match g with
  | (a, b, c) =>
      count_row p a
    + count_row p b
    + count_row p c
  end.

Lemma count_set :
  forall p pos g, 1 + count_pawn p g = count_pawn p (set pos g p).
Proof.
  intros.
  destruct g as [[[[a1 b1] c1] [[a2 b2] c2]] [[a3 b3] c3]].
  induction pos; simpl.
  + assert (pawn_eq p p = true) by (apply pawn_eq_eq; reflexivity).
    rewrite H.
Admitted.

  
Lemma count_step :
  forall p q g1 g2, (g1, p) --> (g2, q) -> 1 + count_pawn p g1 = count_pawn p g2.
Proof.
Admitted.
  

Lemma score_bounds :
  forall p q g, (game_start, p) -->> (g, q) ->
    (count_pawn I g = 1 + count_pawn O g) \/
    (count_pawn O g = 1 + count_pawn I g).
Proof.
  intros.
  inversion H.
  - inversion H0; simpl.
    destruct p0; simpl.
Admitted.