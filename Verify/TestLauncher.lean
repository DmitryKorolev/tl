/- Minimal test supervisor: an imported initializer cannot turn an early
   status-zero exit into a successful test run without the harness marker. -/
import Verify.Supervise

open Tl.Verify

def main (args : List String) : IO UInt32 :=
  launchSiblingWorker (testRequestCompletionProtocol args) args.toArray true
