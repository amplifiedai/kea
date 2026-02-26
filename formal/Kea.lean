-- Kea Type System Formalization
-- Lean 4 formalization of Kea's Remy-style row polymorphism and HM inference.
-- See FORMAL.md at the repo root for the Rust ↔ Lean mapping.

import Kea.Ty
import Kea.Substitution
import Kea.WellFormed
import Kea.FreeVars
import Kea.OccursCheck
import Kea.LacksConstraints
import Kea.Unify
import Kea.Generalize
import Kea.Typing
import Kea.Properties.SubstIdempotent
import Kea.Properties.SubstCompose
import Kea.Properties.SubstBridge
import Kea.Properties.WfSubstitution
import Kea.Properties.WfRename
import Kea.Properties.WfGeneralize
import Kea.Properties.WfEffectRowLadder
import Kea.Properties.HandlerEffectRemoval
import Kea.Properties.HandlerAbsentEffectNoop
import Kea.Properties.ResumeLinearity
import Kea.Properties.HandlerTypingContracts
import Kea.Properties.EffectOperationTyping
import Kea.Properties.TailResumptiveClassification
import Kea.Properties.TailCapabilityComposition
import Kea.Properties.NestedHandlerCompositionContracts
import Kea.Properties.FailResultContracts
import Kea.Properties.EffectPolymorphismSoundness
import Kea.Properties.CatchTypingBridge
import Kea.Properties.HigherOrderCatchContracts
import Kea.Properties.WfUnify
import Kea.Properties.WfUnifyExtends
import Kea.Properties.UnifyReflexive
import Kea.Properties.UnifyConsistent
import Kea.Properties.UnifyExtends
import Kea.Properties.OccursCheckSound
import Kea.Properties.RowFieldsSorted
import Kea.Properties.RemyPreservesLabels
import Kea.Properties.LacksBlocksDuplicate
import Kea.Properties.DecomposeFields
