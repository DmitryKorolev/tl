/- The retained npm-launcher public-process corpus. The native runner writes
this fixture into isolated scratch; it is test code, never release policy.
Keep its static-shell and loader observations intact when changing orchestration. -/
namespace Release.Hermetic

def launcherFixture : String :=
  "#!/bin/sh\n" ++
  "set -eu\n" ++
  "source_launcher=/scratch/packed/package/bin/tl\n" ++
  "work=/scratch/launcher\n" ++
  "failures=0\n" ++
  "\n" ++
  "note() {\n" ++
  "  if [ \"$1\" -eq 0 ]; then\n" ++
  "    echo \"  ok   $2\"\n" ++
  "  else\n" ++
  "    echo \"  FAIL $2\" >&2\n" ++
  "    failures=$((failures + 1))\n" ++
  "  fi\n" ++
  "}\n" ++
  "\n" ++
  "prepare() {\n" ++
  "  name=$1\n" ++
  "  observed_os=$2\n" ++
  "  observed_arch=$3\n" ++
  "  observed_libc=$4\n" ++
  "  case_root=\"$work/$name\"\n" ++
  "  rm -rf \"$case_root\"\n" ++
  "  mkdir -p \"$case_root/tl/bin\" \"$case_root/observe\"\n" ++
  "  cp \"$source_launcher\" \"$case_root/tl/bin/tl\"\n" ++
  "  chmod 0755 \"$case_root/tl/bin/tl\"\n" ++
  "  cat > \"$case_root/observe/uname\" <<UNAME_STUB\n" ++
  "#!/bin/sh\n" ++
  "printf '%s\\n' \"\\${1-}\" >> '$case_root/uname-calls'\n" ++
  "case \\${1-} in\n" ++
  "  -s) printf '%s\\n' '$observed_os' ;;\n" ++
  "  -m) printf '%s\\n' '$observed_arch' ;;\n" ++
  "  *) printf '%s\\n' '$observed_os' ;;\n" ++
  "esac\n" ++
  "UNAME_STUB\n" ++
  "  chmod 0755 \"$case_root/observe/uname\"\n" ++
  "  rm -f /lib64/ld-linux-x86-64.so.2 /lib/ld-linux-aarch64.so.1 /lib/ld-musl-*.so.1\n" ++
  "  case $observed_libc in\n" ++
  "    glibc) : > /lib64/ld-linux-x86-64.so.2; : > /lib/ld-musl-test.so.1 ;;\n" ++
  "    arm64-only) : > /lib/ld-linux-aarch64.so.1 ;;\n" ++
  "    arm64-with-musl) : > /lib/ld-linux-aarch64.so.1; : > /lib/ld-musl-test.so.1 ;;\n" ++
  "    musl) : > /lib/ld-musl-test.so.1 ;;\n" ++
  "    neither) : ;;\n" ++
  "    *) echo \"launcher suite: unknown libc observation '$observed_libc'\" >&2; exit 2 ;;\n" ++
  "  esac\n" ++
  "}\n" ++
  "\n" ++
  "binary_path() {\n" ++
  "  target=$1\n" ++
  "  layout=$2\n" ++
  "  case $layout in\n" ++
  "    hoisted) printf '%s\\n' \"$case_root/tl-bin-$target/bin/tl\" ;;\n" ++
  "    nested) printf '%s\\n' \"$case_root/tl/node_modules/@taskloop/tl-bin-$target/bin/tl\" ;;\n" ++
  "    *) echo \"launcher suite: unknown package layout '$layout'\" >&2; exit 2 ;;\n" ++
  "  esac\n" ++
  "}\n" ++
  "\n" ++
  "plant() {\n" ++
  "  target=$1\n" ++
  "  layout=$2\n" ++
  "  mode=$3\n" ++
  "  candidate=$(binary_path \"$target\" \"$layout\")\n" ++
  "  mkdir -p \"$(dirname -- \"$candidate\")\"\n" ++
  "  printf '#!/bin/sh\\nprintf \"selected %s\\\\n\" \"$*\"\\n' \"$target\" > \"$candidate\"\n" ++
  "  chmod \"$mode\" \"$candidate\"\n" ++
  "}\n" ++
  "\n" ++
  "drive() {\n" ++
  "  run_status=0\n" ++
  "  run_out=$(PATH=\"$case_root/observe:$PATH\" \"$case_root/tl/bin/tl\" \"$@\" 2>&1) || run_status=$?\n" ++
  "}\n" ++
  "\n" ++
  "selection() {\n" ++
  "  name=$1; observed_os=$2; observed_arch=$3; observed_libc=$4\n" ++
  "  target=$5; layout=$6\n" ++
  "  prepare \"$name\" \"$observed_os\" \"$observed_arch\" \"$observed_libc\"\n" ++
  "  plant \"$target\" \"$layout\" 0755\n" ++
  "  drive one \"two three\"\n" ++
  "  note \"$([ \"$run_status\" -eq 0 ] && [ \"$run_out\" = \"selected $target\" ] && echo 0 || echo 1)\" \\\n" ++
  "    \"$name selects $layout @taskloop/tl-bin-$target\"\n" ++
  "}\n" ++
  "\n" ++
  "echo \"npm launcher hermetic suite:\"\n" ++
  "rm -rf \"$work\"\n" ++
  "mkdir -p \"$work\"\n" ++
  "note \"$([ /bin/sh -ef /scratch/static/bin/busybox.static ] && echo 0 || echo 1)\" \\\n" ++
  "  \"the launcher suite reaches the static shell fixture\"\n" ++
  "source_digest=$(sha256sum \"$source_launcher\" | cut -d' ' -f1)\n" ++
  "\n" ++
  "selection darwin-arm64 Darwin arm64 musl darwin-arm64 hoisted\n" ++
  "selection darwin-x64 Darwin x86_64 musl darwin-x64 hoisted\n" ++
  "selection linux-arm64 Linux arm64 glibc linux-arm64 hoisted\n" ++
  "selection linux-x64 Linux x86_64 glibc linux-x64 hoisted\n" ++
  "selection linux-aarch64-alias Linux aarch64 glibc linux-arm64 hoisted\n" ++
  "selection linux-amd64-alias Linux amd64 glibc linux-x64 hoisted\n" ++
  "selection nested-layout Linux x86_64 glibc linux-x64 nested\n" ++
  "\n" ++
  "prepare nested-after-unusable Linux x86_64 glibc\n" ++
  "plant linux-x64 hoisted 0644\n" ++
  "plant linux-x64 nested 0755\n" ++
  "drive\n" ++
  "note \"$([ \"$run_status\" -eq 0 ] && [ \"$run_out\" = 'selected linux-x64' ] && echo 0 || echo 1)\" \\\n" ++
  "  \"an unusable hoisted candidate does not hide an executable nested one\"\n" ++
  "\n" ++
  "prepare native-windows MINGW64_NT-10.0 x86_64 glibc\n" ++
  "drive\n" ++
  "note \"$([ \"$run_status\" -eq 1 ] && printf '%s' \"$run_out\" | grep -q WSL2 && echo 0 || echo 1)\" \\\n" ++
  "  \"native Windows refuses with WSL2 guidance\"\n" ++
  "\n" ++
  "prepare unsupported-os FreeBSD amd64 glibc\n" ++
  "drive\n" ++
  "note \"$([ \"$run_status\" -eq 1 ] && printf '%s' \"$run_out\" | grep -q \"unsupported operating system 'FreeBSD'\" && echo 0 || echo 1)\" \\\n" ++
  "  \"an unsupported operating system is named\"\n" ++
  "\n" ++
  "prepare unsupported-cpu Linux riscv64 glibc\n" ++
  "drive\n" ++
  "note \"$([ \"$run_status\" -eq 1 ] && printf '%s' \"$run_out\" | grep -q \"unsupported CPU architecture 'riscv64'\" && echo 0 || echo 1)\" \\\n" ++
  "  \"an unsupported CPU architecture is named\"\n" ++
  "\n" ++
  "prepare missing-package Linux x86_64 glibc\n" ++
  "drive\n" ++
  "note \"$([ \"$run_status\" -eq 1 ] && printf '%s' \"$run_out\" | grep -q 'not installed' && printf '%s' \"$run_out\" | grep -q optional && echo 0 || echo 1)\" \\\n" ++
  "  \"a missing platform package names the cause and repair\"\n" ++
  "\n" ++
  "prepare mismatched-package Darwin x86_64 musl\n" ++
  "plant darwin-arm64 hoisted 0755\n" ++
  "drive\n" ++
  "note \"$([ \"$run_status\" -eq 1 ] && printf '%s' \"$run_out\" | grep -q 'what is installed: tl-bin-darwin-arm64' && printf '%s' \"$run_out\" | grep -q Rosetta && echo 0 || echo 1)\" \\\n" ++
  "  \"an installed package for another architecture explains npm selection\"\n" ++
  "\n" ++
  "prepare non-executable Linux x86_64 glibc\n" ++
  "plant linux-x64 hoisted 0644\n" ++
  "drive\n" ++
  "note \"$([ \"$run_status\" -eq 1 ] && printf '%s' \"$run_out\" | grep -q 'exists but is not executable' && printf '%s' \"$run_out\" | grep -q 'chmod +x' && echo 0 || echo 1)\" \\\n" ++
  "  \"a present non-executable package names the mode repair\"\n" ++
  "\n" ++
  "prepare musl-missing Linux x86_64 musl\n" ++
  "drive\n" ++
  "note \"$([ \"$run_status\" -eq 1 ] && printf '%s' \"$run_out\" | grep -q 'uses musl libc' && printf '%s' \"$run_out\" | grep -q 'was never installed' && echo 0 || echo 1)\" \\\n" ++
  "  \"musl explains why npm omitted the package\"\n" ++
  "\n" ++
  "prepare musl-present Linux x86_64 musl\n" ++
  "plant linux-x64 hoisted 0755\n" ++
  "drive\n" ++
  "note \"$([ \"$run_status\" -eq 1 ] && printf '%s' \"$run_out\" | grep -q 'uses musl libc' && printf '%s' \"$run_out\" | grep -q 'glibc-based image' && echo 0 || echo 1)\" \\\n" ++
  "  \"musl refuses a glibc binary even when a package manager installed it\"\n" ++
  "\n" ++
  "# Cross both on_musl call sites with every previously absent observation.\n" ++
  "for observation in arm64-only arm64-with-musl neither; do\n" ++
  "  selection \"$observation-present\" Linux aarch64 \"$observation\" linux-arm64 hoisted\n" ++
  "  prepare \"$observation-missing\" Linux aarch64 \"$observation\"\n" ++
  "  drive\n" ++
  "  note \"$([ \"$run_status\" -eq 1 ] && printf '%s' \"$run_out\" | grep -q 'not installed' && ! printf '%s' \"$run_out\" | grep -q 'uses musl libc' && echo 0 || echo 1)\" \\\n" ++
  "    \"$observation without a package reaches the missing-package repair\"\n" ++
  "  for variant in present missing; do\n" ++
  "    observed_case=\"$work/$observation-$variant\"\n" ++
  "    note \"$(grep -qx -- -s \"$observed_case/uname-calls\" && grep -qx -- -m \"$observed_case/uname-calls\" && echo 0 || echo 1)\" \\\n" ++
  "      \"$observation-$variant reaches both uname collaborators\"\n" ++
  "    observed_digest=$(sha256sum \"$observed_case/tl/bin/tl\" | cut -d' ' -f1)\n" ++
  "    note \"$([ \"$source_digest\" = \"$observed_digest\" ] && echo 0 || echo 1)\" \\\n" ++
  "      \"$observation-$variant executes the packed launcher bytes\"\n" ++
  "  done\n" ++
  "done\n" ++
  "\n" ++
  "prepare relative-symlink Linux x86_64 glibc\n" ++
  "plant linux-x64 hoisted 0755\n" ++
  "mkdir -p \"$case_root/.bin\"\n" ++
  "ln -s ../tl/bin/tl \"$case_root/.bin/tl\"\n" ++
  "run_status=0\n" ++
  "run_out=$(PATH=\"$case_root/observe:$PATH\" \"$case_root/.bin/tl\" 2>&1) || run_status=$?\n" ++
  "note \"$([ \"$run_status\" -eq 0 ] && [ \"$run_out\" = 'selected linux-x64' ] && echo 0 || echo 1)\" \\\n" ++
  "  \"a relative npm bin symlink resolves to the package\"\n" ++
  "\n" ++
  "prepare absolute-symlink Linux x86_64 glibc\n" ++
  "plant linux-x64 hoisted 0755\n" ++
  "mkdir -p \"$case_root/.global\"\n" ++
  "ln -s \"$case_root/tl/bin/tl\" \"$case_root/.global/tl\"\n" ++
  "run_status=0\n" ++
  "run_out=$(PATH=\"$case_root/observe:$PATH\" \"$case_root/.global/tl\" 2>&1) || run_status=$?\n" ++
  "note \"$([ \"$run_status\" -eq 0 ] && [ \"$run_out\" = 'selected linux-x64' ] && echo 0 || echo 1)\" \\\n" ++
  "  \"an absolute global-style symlink resolves to the package\"\n" ++
  "\n" ++
  "prepare process-contract Linux x86_64 glibc\n" ++
  "candidate=$(binary_path linux-x64 hoisted)\n" ++
  "mkdir -p \"$(dirname -- \"$candidate\")\"\n" ++
  "cat > \"$candidate\" <<'PROCESS_STUB'\n" ++
  "#!/bin/sh\n" ++
  "IFS= read -r line\n" ++
  "printf 'stdin=%s\\n' \"$line\"\n" ++
  "printf '<%s>\\n' \"$@\"\n" ++
  "printf 'native stderr\\n' >&2\n" ++
  "exit 42\n" ++
  "PROCESS_STUB\n" ++
  "chmod 0755 \"$candidate\"\n" ++
  "run_status=0\n" ++
  "printf 'stream input\\n' | PATH=\"$case_root/observe:$PATH\" \"$case_root/tl/bin/tl\" one \"two three\" \\\n" ++
  "  > \"$case_root/stdout\" 2> \"$case_root/stderr\" || run_status=$?\n" ++
  "note \"$([ \"$run_status\" -eq 42 ] && echo 0 || echo 1)\" \\\n" ++
  "  \"the native binary's exit status passes through\"\n" ++
  "note \"$(grep -qx 'stdin=stream input' \"$case_root/stdout\" && grep -qx '<one>' \"$case_root/stdout\" && grep -qx '<two three>' \"$case_root/stdout\" && echo 0 || echo 1)\" \\\n" ++
  "  \"stdin and unsplit arguments reach the native binary\"\n" ++
  "note \"$(grep -qx 'native stderr' \"$case_root/stderr\" && echo 0 || echo 1)\" \\\n" ++
  "  \"stderr remains the native binary's stream\"\n" ++
  "\n" ++
  "prepare process-identity Linux x86_64 glibc\n" ++
  "candidate=$(binary_path linux-x64 hoisted)\n" ++
  "mkdir -p \"$(dirname -- \"$candidate\")\"\n" ++
  "printf '#!/bin/sh\\nprintf \"%%s\\\\n\" \"$$\" > \"%s\"\\n' \"$case_root/native-pid\" > \"$candidate\"\n" ++
  "chmod 0755 \"$candidate\"\n" ++
  "PATH=\"$case_root/observe:$PATH\" \"$case_root/tl/bin/tl\" &\n" ++
  "launcher_pid=$!\n" ++
  "wait \"$launcher_pid\"\n" ++
  "native_pid=$(cat \"$case_root/native-pid\")\n" ++
  "note \"$([ \"$native_pid\" = \"$launcher_pid\" ] && echo 0 || echo 1)\" \\\n" ++
  "  \"exec gives the native binary the launcher's process identity\"\n" ++
  "\n" ++
  "prepare signal-contract Linux x86_64 glibc\n" ++
  "candidate=$(binary_path linux-x64 hoisted)\n" ++
  "mkdir -p \"$(dirname -- \"$candidate\")\"\n" ++
  "cat > \"$candidate\" <<SIGNAL_STUB\n" ++
  "#!/bin/sh\n" ++
  "child=''\n" ++
  "trap '[ -z \"\\$child\" ] || kill \"\\$child\" 2>/dev/null || true; exit 7' TERM\n" ++
  "printf '%s\\n' \"\\$\\$\" > '$case_root/native-ready'\n" ++
  "sleep 30 &\n" ++
  "child=\\$!\n" ++
  "wait \"\\$child\"\n" ++
  "SIGNAL_STUB\n" ++
  "chmod 0755 \"$candidate\"\n" ++
  "PATH=\"$case_root/observe:$PATH\" \"$case_root/tl/bin/tl\" &\n" ++
  "launcher_pid=$!\n" ++
  "waited=0\n" ++
  "while [ ! -s \"$case_root/native-ready\" ] && [ \"$waited\" -lt 100 ]; do\n" ++
  "  sleep 0.05\n" ++
  "  waited=$((waited + 1))\n" ++
  "done\n" ++
  "kill -TERM \"$launcher_pid\" 2>/dev/null || true\n" ++
  "run_status=0\n" ++
  "wait \"$launcher_pid\" || run_status=$?\n" ++
  "note \"$([ \"$run_status\" -eq 7 ] && echo 0 || echo 1)\" \\\n" ++
  "  \"SIGTERM reaches the native binary rather than a forwarding wrapper\"\n" ++
  "\n" ++
  "copied_digest=$(sha256sum \"$work/linux-x64/tl/bin/tl\" | cut -d' ' -f1)\n" ++
  "note \"$([ \"$source_digest\" = \"$copied_digest\" ] && echo 0 || echo 1)\" \\\n" ++
  "  \"the suite ran byte-identical launcher copies\"\n" ++
  "if [ \"$failures\" -ne 0 ]; then\n" ++
  "  echo \"npm launcher hermetic suite: $failures broken case(s)\" >&2\n" ++
  "  exit 1\n" ++
  "fi\n" ++
  "echo \"npm launcher hermetic suite: passed\"\n" ++
  ""

end Release.Hermetic
