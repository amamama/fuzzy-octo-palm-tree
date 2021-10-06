import Std.Data.HashSet
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
def NextPlayerType := Player → Player
def NextPlayerType.default: NextPlayerType
| player₁ => player₂
| player₂ => player₃
| player₃ => player₄
| player₄ => player₁
instance : Inhabited NextPlayerType where default := NextPlayerType.default

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
  nextplayer: NextPlayerType
  deriving Inhabited
def Zone := Std.HashSet Nat
  deriving Inhabited
structure PlayerState where
  hand: Zone
  deck: Zone
  --life: Int
  --graveyard: Zone
  --pool: Int
  passPriority: Bool
  deriving Inhabited
def PlayerStateStore := Player → PlayerState
  deriving Inhabited
def UpdatePlayerStateStore (st: PlayerStateStore) (p: Player) (ps: PlayerState): PlayerStateStore :=
  λp' => if p = p' then ps else st p'
def PlayerStateStore.getOp (self: PlayerStateStore) (idx: Player) : PlayerState := self idx
notation:100 st "[ " pl " ↦ " ps " ]" => UpdatePlayerStateStore st pl ps

#print Std.HashSet

inductive PriorityOwner
| none
| player(p: Player)
deriving Inhabited
structure GameState where
  setting: GameSetting
  turnList: TurnList
  phaseList: PhaseList
  priority: PriorityOwner
  didEveryPlayerPassTheirPriority: Bool
  playerStates: PlayerStateStore
  deriving Inhabited

inductive PriorityRel: GameState → GameState → Prop
| passPriority: ∀(s: GameState) (p: Player),
  s.priority = PriorityOwner.player p ∧ s.playerStates[p].passPriority = false -- かつ ターン起因処理と誘発型能力を積み終わった
  → PriorityRel s
  {
    s with
    priority := PriorityOwner.player (s.setting.nextplayer p),
    playerStates :=
      s.playerStates[p ↦
        {
          s.playerStates[p] with
          passPriority := true
        }
      ]
  } -- MEMO: koko motto iikannji ni sitai
-- その他の行動をできるようにする

inductive ProgressPhaseRel: GameState → GameState → Prop
| nextStep: ∀(s: GameState) (p: Phase) (next: PhaseList),
  s.phaseList = p::next ∧ s.didEveryPlayerPassTheirPriority = true
  → ProgressPhaseRel s {s with phaseList := next, didEveryPlayerPassTheirPriority := false}
  -- ターン起因処理と状況起因処理，誘発型能力の誘発をした状態にする
-- | untapStep
-- アンタップ・ステップのターン起因処理関連はここで行わないといけない
| transStep: ∀s s₁ s₂,
  ProgressPhaseRel s s₁
  → ProgressPhaseRel s₁ s₂
  → ProgressPhaseRel s s₂

inductive ProgressTurnRel: GameState → GameState → Prop
| nextTurn:
  ∀ (s: GameState) (p: Player),
  s.turnList = [p] ∧ s.phaseList = [Phase.ending cleanup]
  → ProgressTurnRel s {s with turnList := [s.setting.nextplayer p], phaseList := defaultPhaseList}
  -- ターン起因処理と状況起因処理，誘発型能力の誘発をした状態にする．
| extraTurn:
  ∀ (s: GameState) (p : Player) (next: TurnList),
  s.turnList = p::next ∧ s.phaseList = [Phase.ending cleanup]
  → ProgressTurnRel s {s with turnList := next, phaseList := defaultPhaseList}
| transTurn: ∀s s₁ s₂,
  ProgressTurnRel s s₁
  → ProgressTurnRel s₁ s₂
  → ProgressTurnRel s s₂