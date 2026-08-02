/- Minimal supervisor: an audited worker must reach its final verdict marker. -/
import Verify.Supervise

open Tl.Verify

def main : IO UInt32 := do
  launchSiblingWorker verifierCompletionProtocol
