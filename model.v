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

Definition free (pos : position) (board : game) : bool :=
  pawn_eq (get pos board) U.

Definition state : Type := (game * pawn)%type.

Definition winI (board : game) : bool :=
  diagI board || rowI board.

Definition winO (board : game) : bool :=
  diagO board || rowO board.

Definition game_done (board : game) : bool :=
  winI board || winO board.

Inductive step : state -> state -> Prop :=
  | play_free : forall pos p board,
    free pos board = true ->
    game_done board = false ->
    step (board, p) (set pos board p, inv p).

Inductive steps : state -> state -> Prop :=
  | steps_one   : forall s1 s2,
    step s1 s2 -> steps s1 s2
  | steps_trans : forall s1 s2 s3,
    step s1 s2 -> steps s2 s3 -> steps s1 s3.

Example opening :
  game_done game_start = false.
Proof.
  cbn. reflexivity.
Qed.

Example ending :
  exists s, steps (game_start, O) (s, I) /\ winO s = true.
Proof.
  eexists. split.
  - eapply steps_trans.
    apply (play_free A1 O _); auto.
    cbn.
    eapply steps_trans.
    apply (play_free A2 I _); auto.
    cbn.
    eapply steps_trans.
    apply (play_free B1 O _); auto.
    cbn.
    eapply steps_trans.
    apply (play_free B2 I _); auto.
    cbn.
    eapply steps_one.
    apply (play_free C1 O _); auto.
  - reflexivity.
Qed.










