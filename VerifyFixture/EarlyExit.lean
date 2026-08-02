/- Adversarial verifier fixture: importing extensions would terminate the gate. -/
namespace Tl.Tests.Fixtures

def loadedWithoutRunning : Bool := true

initialize earlyExitCanary : Unit ← IO.Process.exit 23

end Tl.Tests.Fixtures
