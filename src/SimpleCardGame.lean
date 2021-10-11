import Std.Data.HashSet
import Std.Data.AssocList
/-
TODO: ステップの進行時に誘発型能力の誘発をできるようにする．
置換型能力を取り扱うため，eventキューを用意し，ゲーム内の行動は一旦このキューにエンキューされる．
  置換型能力は置換するイベントと置換後のイベントで表される．
  ある状態での置換型能力の集合を用意しておき，eventキューの先端のイベントでその集合にfilterし対応する置換型能力を適用する
  置換型能力に置換する優先度を定義するが，同じ場合はここにユーザーの選択が入る
  「禁止する」効果は「何もしない」に置換する置換型効果として扱い，最も高い優先度を持つ．
ループの扱い
  ある状態である行動をしたときに何らかの能力（群）が生成され，ユーザが行動する前に同じ能力が有限個の違いを除いた状態s1とs2で生成されたとき，無限ループとする．
  ↑に加えてユーザの行動が入る場合，「前回と同じ行動をする」という前提を加えれば無限ループになるとき，ループとする．
  ループが存在するとき，有限回後にユーザの行動を変化させなければならない．
  基本的に能力は強制効果「〜する」であり，無限ループになるときに限りしないことを選択できる．
  任意効果「してもよい」がループを形成する場合，↑に準ずる．
  ループを形成する場合，有限個の違いを変数化して一気に処理したいが厳しそう
-/
inductive Player: Type
| player₁
| player₂
| player₃
| player₄
deriving DecidableEq
open Player
instance : Inhabited Player where default := player₁
def NextPlayerType := ∃f: Player → Player, ∀p: Player, ¬f p = p
def NextPlayerType.default: NextPlayerType := by {
  let f 
  | player₁ => player₂
  | player₂ => player₃
  | player₃ => player₄
  | player₄ => player₁
  exists f;
  intro p';
  cases p';
  all_goals {
    intro;
    contradiction;
  }
}
instance : Inhabited NextPlayerType where default := NextPlayerType.default
def PlayerToNat: Player → Nat
| player₁ => 0
| player₂ => 1
| player₃ => 2
| player₄ => 3

inductive BeginningPhase: Type
| untap -- MEMO: namae kaeru yotei
| upkeep
| draw
open BeginningPhase

inductive CombatPhase: Type
| beginningOfCombat
| declareAtackers
| declareBlockers
| combatDamage
| endOfCombat
open CombatPhase

inductive EndingPhase: Type
| ending
| cleanup
open EndingPhase

inductive Phase: Type
| beginning (step: BeginningPhase)
| main
| combat (step: CombatPhase)
| ending (step: EndingPhase)
open Phase
def defaultBeginningPhase := [
  beginning untap,
  beginning upkeep,
  beginning draw
]
def defaultCombatPhase := [
  combat beginningOfCombat,
  combat declareAtackers,
  combat declareBlockers,
  combat combatDamage,
  combat endOfCombat
]
def defaultEndingPhase := [
  ending ending,
  ending cleanup
]

def TurnList := List Player
  deriving Inhabited
def PhaseList := List Phase
  deriving Inhabited
def defaultPhaseList :=
  defaultBeginningPhase
  ++ [main]
  ++ defaultCombatPhase
  ++ [main]
  ++ defaultEndingPhase

structure GameSetting where
  joinedPlayers: Std.AssocList Player Bool
  nextplayer: NextPlayerType
instance : Inhabited GameSetting where
  default := {
    joinedPlayers:= 
      Std.AssocList.empty
      |> Std.AssocList.cons player₁ true
      |> Std.AssocList.cons player₂ true
      |> Std.AssocList.cons player₃ true
      |> Std.AssocList.cons player₄ true,
      nextplayer := NextPlayerType.default,
  }
def Zone := Std.HashSet Nat
  deriving Inhabited
structure PlayerState where
  hand: Zone
  deck: Zone
  --life: Int
  --graveyard: Zone
  --pool: Int
  passPriority: Bool
def PlayerState.default: PlayerState := {
  hand := Inhabited.default,
  deck := Inhabited.default,
  --life: Int
  --graveyard: Zone
  --pool: Int
  passPriority := false
}
instance : Inhabited PlayerState where
  default := PlayerState.default  

structure PlayerStateStore where
  p₁: PlayerState
  p₂: PlayerState
  p₃: PlayerState
  p₄: PlayerState
def PlayerStateStore.default: PlayerStateStore := {
  p₁:= Inhabited.default, 
  p₂:= Inhabited.default,
  p₃:= Inhabited.default,
  p₄:= Inhabited.default,
}
instance : Inhabited PlayerStateStore where
  default := PlayerStateStore.default

def UpdatePlayerStateStore (st: PlayerStateStore) (idx: Player) (ps: PlayerState): PlayerStateStore :=
  match idx with
  | player₁ => {st with p₁ := ps}
  | player₂ => {st with p₂ := ps}
  | player₃ => {st with p₃ := ps}
  | player₄ => {st with p₄ := ps}
def PlayerStateStore.getOp (self: PlayerStateStore) (idx: Player) : PlayerState :=
  match idx with
  | player₁ => self.p₁
  | player₂ => self.p₂
  | player₃ => self.p₃
  | player₄ => self.p₄
notation:100 st "[ " pl " ↦ " ps " ]" => UpdatePlayerStateStore st pl ps
#print Std.HashSet

inductive PriorityOwner
| none
| player(p: Player)
--deriving Inhabited
--honto ha default wo none ni sinaito ikenai
instance : Inhabited PriorityOwner where
  default := PriorityOwner.player player₁

structure GameState where
  setting: GameSetting
  turnList: TurnList
  phaseList: PhaseList
  priority: PriorityOwner
  didEveryPlayerPassTheirPriority: Bool
  playerStates: PlayerStateStore
def GameState.default: GameState := {
  setting := Inhabited.default,
  turnList := [player₁],
  phaseList := defaultPhaseList,
  priority := Inhabited.default,
  didEveryPlayerPassTheirPriority := Inhabited.default,
  playerStates := Inhabited.default,
}

instance : Inhabited GameState where
  default := GameState.default

def updatePriority (ps: PlayerStateStore) (pl: Player) (p: Bool) :=
  ps[pl ↦ {ps[pl] with passPriority := p}]
def updateEveryPriority (ps: PlayerStateStore) (p: Bool) :=
  let ps₁ := updatePriority ps player₁ p;
  let ps₂ := updatePriority ps₁ player₂ p;
  let ps₃ := updatePriority ps₂ player₃ p;
  updatePriority ps₃ player₄ p

#check @Exists
#check @Sigma

inductive PriorityRel: GameState → GameState → Prop
| passPriority: ∀(s: GameState) (p: Player),
  s.priority = PriorityOwner.player p ∧ s.playerStates[p].passPriority = false -- かつ ターン起因処理と誘発型能力を積み終わった
  → PriorityRel s
  {
    s with
    priority := PriorityOwner.player (s.setting.nextplayer.1 p),
    playerStates := updatePriority s.playerStates p true
  } -- MEMO: koko motto iikannji ni sitai
| transPriority: ∀s₁ s₂ s₃,
  PriorityRel s₁ s₂
  → PriorityRel s₂ s₃
  → PriorityRel s₁ s₃
| everyPlayerPassTheirPriority: ∀(s: GameState) (p: Player) (tl: TurnList),
  s.priority = PriorityOwner.player p
  ∧ s.turnList = p :: tl
  ∧ (∀(p: Player),
    Std.AssocList.contains p s.setting.joinedPlayers
    ∧ Std.AssocList.findEntry? p s.setting.joinedPlayers = some (p, true)
    ∧ s.playerStates[p].passPriority = true)
  → PriorityRel s
  {
    s with
    playerStates := updateEveryPriority s.playerStates false
  }
-- その他の行動をできるようにする


inductive ProgressPhaseRel: GameState → GameState → Prop
| nextStep: ∀(s: GameState) (p: Phase) (next: PhaseList),
  s.phaseList = p::next ∧ s.didEveryPlayerPassTheirPriority = true
  → ProgressPhaseRel s {s with phaseList := next, didEveryPlayerPassTheirPriority := false}
  -- ターン起因処理と状況起因処理，誘発型能力の誘発をした状態にする
  -- これnextがcleanupのときも進行してやばいね
-- | untapStep
-- アンタップ・ステップのターン起因処理関連はここで行わないといけない
| transStep: ∀s₁ s₂ s₃,
  ProgressPhaseRel s₁ s₂
  → ProgressPhaseRel s₂ s₃
  → ProgressPhaseRel s₁ s₃
| priorityRel: ∀s₁ s₂ s₃,
  PriorityRel s₁ s₂
  → ProgressPhaseRel s₂ s₃
  → ProgressPhaseRel s₁ s₃


inductive ProgressTurnRel: GameState → GameState → Prop
| nextTurn:
  ∀ (s: GameState) (p: Player),
  s.turnList = [p] ∧ s.phaseList = [Phase.ending cleanup]
  → ProgressTurnRel s {s with turnList := [s.setting.nextplayer.1 p], phaseList := defaultPhaseList}
  -- ターン起因処理と状況起因処理，誘発型能力の誘発をした状態にする．
| extraTurn:
  ∀ (s: GameState) (p : Player) (next: TurnList),
  ¬ next = [] 
  ∧ s.turnList = p::next ∧ s.phaseList = [Phase.ending cleanup]
  → ProgressTurnRel s {s with turnList := next, phaseList := defaultPhaseList}
| transTurn: ∀s₁ s₂ s₃,
  ProgressTurnRel s₁ s₂
  → ProgressTurnRel s₂ s₃
  → ProgressTurnRel s₁ s₃
| phaseRel: ∀s₁ s₂ s₃,
  ProgressPhaseRel s₁ s₂
  → ProgressTurnRel s₂ s₃
  → ProgressTurnRel s₁ s₃

#print List

theorem proofOfPriorityRel : ∀(s: GameState) (p: Player),
s.priority = (PriorityOwner.player p)
∧ s.playerStates[p].passPriority = false
→ ∃s', PriorityRel s s'
∧ s'.priority = PriorityOwner.player (s.setting.nextplayer.1 p)
∧ s.playerStates[s.setting.nextplayer.1 p].passPriority = s'.playerStates[s.setting.nextplayer.1 p].passPriority := by {
  intros s p h;
  have h1 := (PriorityRel.passPriority s p h);
  let s' := {
    s with
    priority := PriorityOwner.player (s.setting.nextplayer.1 p),
    playerStates := updatePriority s.playerStates p true
  };
  have h2: s'.priority = PriorityOwner.player (s.setting.nextplayer.1 p) := rfl;
  have h3: s.playerStates[s.setting.nextplayer.1 p].passPriority = s'.playerStates[s.setting.nextplayer.1 p].passPriority := by {
    generalize h4: s.setting.nextplayer.1 p = p';
    have h5 : p' ≠ p := by {
        have h6 := s.setting.nextplayer.2 p;
        rw [←h4];
        assumption;
    }

  }
  have h4 := And.intro h1 (And.intro h2 h3);
  exact Exists.intro s' h4;
}

example : ProgressTurnRel GameState.default {GameState.default with turnList := [player₂]} := by {
  let s: GameState := GameState.default;
  have h0: s = GameState.default := rfl;
  have h1: s.turnList = [player₁] := rfl;
  have h2: s.priority = PriorityOwner.player player₁ := rfl;
  have h3: s.playerStates[player₁].passPriority = false := rfl;
  rw [h0] at *;
  have h4 := And.intro h2 h3;
  /-
  have h5 := PriorityRel.passPriority GameState.default player₁ h4;
  let s1 := {
    s with
    priority := PriorityOwner.player (s.setting.nextplayer player₁),
    playerStates := updatePriority s.playerStates player₁ true,
  }
  -/
  have ⟨s1, ⟨h5, h6, h7⟩⟩ := proofOfPriorityRel s player₁ h4;
  have h8: s.setting.nextplayer.1 player₁ = player₂ := rfl;
  rw [h8] at h6;
  rw [h8] at h7;
  have h9 := And.intro h6 h7;
}