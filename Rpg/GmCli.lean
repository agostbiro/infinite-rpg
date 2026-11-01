import Rpg.Prompt

/-! Local coding-assistant logins can supply GM data without a separate API key.
Their structured answers still pass the ordinary legality and fairness gates. -/
namespace Rpg.GmCli
open Lean

/-- Keep text blocks only; private thinking and provider metadata are not new instructions. -/
def textContent (j : Json) : String :=
  match j.getStr? with
  | .ok s => s
  | .error _ => String.join ((j.getArr?).toOption.getD #[] |>.toList.filterMap fun block =>
      if (block.getObjValAs? String "type").toOption == some "text" then
        (block.getObjValAs? String "text").toOption else none)

/-- Send the existing GM conversation through stdin, retaining its role labels. -/
def prompt (req : Json) : String :=
  let messages := ((req.getObjValAs? (Array Json) "messages").toOption.getD #[]).map fun msg =>
    json% { role: $((msg.getObjValAs? String "role").toOption.getD "user"),
      content: $(textContent (msg.getObjValD "content")) }
  "Continue the following RPG conversation and answer its last user request. Return only the requested structured game data.\n" ++
    (toJson messages).compress

/-- Disable tools and customizations; authentication stays managed by the installed CLI. -/
def claudeArgs (req : Json) : Array String := #[
  "--safe-mode", "--print", "--tools", "", "--strict-mcp-config", "--no-chrome",
  "--disable-slash-commands", "--no-session-persistence", "--output-format", "json",
  "--permission-prompts", "none", "--model", (req.getObjValAs? String "model").toOption.getD dmModel,
  "--effort", ((req.getObjVal? "output_config" >>= (·.getObjValAs? String "effort")).toOption.getD "medium"),
  "--system-prompt", textContent (req.getObjValD "system"),
  "--json-schema", (req.getObjValD "output_config" |>.getObjValD "format" |>.getObjValD "schema").compress]

/-- Only a successful structured result can become a proposal. Errors remain visible. -/
def parseClaudeReply (body : String) : Reply :=
  match Json.parse body with
  | .error _ => .failed "The local Claude command did not return JSON. Check its login and version."
  | .ok j =>
    if (j.getObjValAs? Bool "is_error").toOption.getD false then
      .failed ((j.getObjValAs? String "result").toOption.getD "The local Claude request failed.")
    else match j.getObjVal? "structured_output" with
    | .ok value =>
      if value == Json.null then .failed "Claude returned no structured game proposal." else
      let text := value.compress
      .ok text (json% [{ type: "text", text: $(text) }])
    | .error _ => .failed "Claude returned no structured game proposal. Check its login and account limits."

-- CLI errors and missing output never turn into successful proposals.
#guard (parseClaudeReply "{\"is_error\":false,\"structured_output\":{\"ready\":true}}").text? == some "{\"ready\":true}"
#guard (parseClaudeReply "{\"is_error\":true,\"result\":\"Sign in first\",\"structured_output\":{}}").text?.isNone
#guard (parseClaudeReply "{\"is_error\":false,\"result\":\"No proposal\"}").text?.isNone
#guard textContent (json% [{ type: "thinking", thinking: "private" }, { type: "text", text: "proposal" }]) == "proposal"

/-- Codex runs in an isolated directory with read-only permissions and external integrations off. -/
def codexArgs (schema output : System.FilePath) : Array String := #[
  "--no-daemon", "exec", "--ignore-user-config", "--ephemeral", "--skip-git-repo-check",
  "--sandbox", "read-only", "--disable", "shell_tool", "--disable", "apps",
  "--disable", "plugins", "--disable", "hooks", "--disable", "multi_agent",
  "--disable", "browser_use", "--disable", "computer_use", "--disable", "image_generation",
  "--color", "never", "--json", "--output-schema", schema.toString,
  "--output-last-message", output.toString, "-"]

/-- A valid JSON result is data for the ordinary decoder, never a command to execute. -/
def parseCodexReply (body : String) : Reply :=
  match Json.parse body with
  | .error _ => .failed "Codex returned no valid JSON game proposal."
  | .ok j =>
    let text := j.compress
    .ok text (json% [{ type: "text", text: $(text) }])

#guard (parseCodexReply "{\"ready\":true}").text? == some "{\"ready\":true}"
#guard (parseCodexReply "").text?.isNone

end Rpg.GmCli
