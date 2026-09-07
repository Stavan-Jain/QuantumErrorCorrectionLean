/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import ProofWidgets.Component.HtmlDisplay

/-!
# Design tokens and stylesheet for the QEC widgets

The single source of truth for how the widgets look: the palette, the `qecw-*`
class stylesheet, and the shared card/header building blocks.

Styling is class-based rather than inline. That is what enables hover states and
transitions (inline styles cannot express `:hover`), per-theme tuning (VS Code
stamps `vscode-dark` / `vscode-light` / `vscode-high-contrast` on the webview
body), and small RPC payloads (a 144-qubit strip carries one class name per cell
instead of a repeated style object).

Every card embeds the stylesheet via `styleTag`; duplicate `<style>` tags in one
webview are idempotent, so cards stay self-contained.
-/

namespace QECWidgets

open Lean ProofWidgets

/-- Shorthand for `Html.element`. -/
def el (tag : String) (attrs : Array (String × Json)) (children : Array Html) : Html :=
  .element tag attrs children

/-- An element carrying only a `style` attribute. -/
def styled (tag : String) (style : Json) (children : Array Html) : Html :=
  el tag #[("style", style)] children

/-- An element carrying (at least) a class. React wants `className`. -/
def cls (tag : String) (className : String) (attrs : Array (String × Json) := #[])
    (children : Array Html := #[]) : Html :=
  el tag (#[("className", Json.str className)] ++ attrs) children

/-- An accent color: hex for strokes/text, `"r, g, b"` for alpha tints. -/
structure Accent where
  /-- `#rrggbb` form. -/
  hex : String
  /-- `"r, g, b"` form, for `rgba(...)` tints. -/
  rgb : String

/-- X operators: coral. -/
def xAccent : Accent := ⟨"#d85a30", "216, 90, 48"⟩

/-- Y operators: teal. -/
def yAccent : Accent := ⟨"#1d9e75", "29, 158, 117"⟩

/-- Z operators: blue. -/
def zAccent : Accent := ⟨"#378add", "55, 138, 221"⟩

/-- Ring color for flagged qubit positions: purple. -/
def markHex : String := "#7f77dd"

/-- Anticommuting Gram cells: red. -/
def antiHex : String := "#e24b4a"

/-- Verdict / state colors (theme variables with sane fallbacks). -/
def okColor : String := "var(--vscode-charts-green, #2ea060)"

/-- See `okColor`. -/
def badColor : String := "var(--vscode-errorForeground, #d16969)"

/-- See `okColor`. -/
def warnColor : String := "var(--vscode-editorWarning-foreground, #c98a1b)"

/-- The `qecw-*` stylesheet. Type scale is 13 px for data, 11 px for meta, 10 px
for micro-labels; data is always in the editor (mono) font, labels in the UI
font; numerals are tabular so indices align. -/
def qecwCss : String :=
  let css := "
.qecw-card{display:flex;gap:10px;padding:10px 12px;margin:4px 0;
 border:1px solid var(--vscode-widget-border,rgba(128,128,128,0.3));
 border-radius:8px;font-family:var(--vscode-font-family,sans-serif)}
.qecw-bar{width:3px;border-radius:2px;flex:none;
 background:var(--vscode-widget-border,rgba(128,128,128,0.2))}
.qecw-body{flex:1;min-width:0}
.qecw-head{display:flex;align-items:baseline;gap:8px;margin-bottom:4px}
.qecw-name{font-family:var(--vscode-editor-font-family,monospace);font-size:11px;
 opacity:.65;word-break:break-all;flex:1;min-width:0}
.qecw-fact{font-size:11px;white-space:nowrap;font-variant-numeric:tabular-nums;
 color:var(--vscode-descriptionForeground,#888)}
.qecw-strip{display:flex;align-items:center;margin-bottom:2px}
.qecw-cell{display:inline-flex;align-items:center;justify-content:center;
 width:18px;height:22px;margin:1px;border-radius:4px;font-size:13px;font-weight:500;
 font-family:var(--vscode-editor-font-family,monospace);
 transition:background-color .12s ease,opacity .12s ease}
.qecw-x{color:@XH;background:rgba(@XR,.13)}
.qecw-x:hover{background:rgba(@XR,.3)}
.qecw-y{color:@YH;background:rgba(@YR,.13)}
.qecw-y:hover{background:rgba(@YR,.3)}
.qecw-z{color:@ZH;background:rgba(@ZR,.13)}
.qecw-z:hover{background:rgba(@ZR,.3)}
.qecw-i{color:var(--vscode-descriptionForeground,#888);opacity:.6}
.qecw-i:hover{opacity:1;background:rgba(128,128,128,.14)}
.qecw-stuck{color:var(--vscode-errorForeground,#d16969)}
.qecw-mark{box-shadow:0 0 0 1.5px @MH}
.qecw-glyph{display:inline-flex;align-items:center;justify-content:center;
 width:20px;height:22px;margin:1px;font-size:13px;font-weight:500;opacity:.85;
 font-family:var(--vscode-editor-font-family,monospace)}
.qecw-rowlabel{display:inline-block;width:30px;text-align:right;margin-right:7px;
 font-size:10px;opacity:.55;font-variant-numeric:tabular-nums;
 font-family:var(--vscode-editor-font-family,monospace)}
.qecw-verdict{display:flex;align-items:center;gap:6px;font-size:11px;font-weight:500;
 margin-top:6px}
.qecw-verdict a{color:inherit;text-decoration:none;
 border-bottom:1px dotted currentColor;cursor:pointer}
.qecw-micro{font-size:10px;color:var(--vscode-descriptionForeground,#888);
 font-variant-numeric:tabular-nums}
.qecw-bit{display:inline-block;width:13px;height:13px;border-radius:3px;margin:1px;
 transition:transform .1s ease}
.qecw-bit:hover{transform:scale(1.3)}
.qecw-bit-x{background:rgba(@XR,.85)}
.qecw-bit-z{background:rgba(@ZR,.85)}
.qecw-bit-0{box-shadow:inset 0 0 0 1px rgba(128,128,128,.25)}
.qecw-bit-diag{background:rgba(128,128,128,.18)}
.qecw-bit-anti{background:@AH}
.qecw-bit-stuck{background:rgba(201,138,27,.5)}
.qecw-svg-grid{stroke:var(--vscode-descriptionForeground,#888);stroke-opacity:.32;
 stroke-width:1;shape-rendering:crispEdges}
.qecw-svg-halo{stroke:var(--vscode-editor-background,#fff);stroke-width:5.5;
 stroke-linecap:round;fill:none}
.qecw-svg-dot{fill:var(--vscode-descriptionForeground,#888);fill-opacity:.65}
.qecw-svg-label{font-size:10px;fill:var(--vscode-descriptionForeground,#888);
 fill-opacity:.85;font-variant-numeric:tabular-nums}
.vscode-dark .qecw-x{color:#e57a50;background:rgba(@XR,.17)}
.vscode-dark .qecw-y{color:#2fb98e;background:rgba(@YR,.17)}
.vscode-dark .qecw-z{color:#61a9e8;background:rgba(@ZR,.17)}
.vscode-high-contrast .qecw-cell{background:transparent !important;
 box-shadow:inset 0 0 0 1px currentColor}
.vscode-high-contrast .qecw-cell.qecw-mark{box-shadow:inset 0 0 0 1px currentColor,
 0 0 0 2px @MH}
.vscode-high-contrast .qecw-bit-0{box-shadow:inset 0 0 0 1px currentColor}
"
  css
    |>.replace "@XH" xAccent.hex |>.replace "@XR" xAccent.rgb
    |>.replace "@YH" yAccent.hex |>.replace "@YR" yAccent.rgb
    |>.replace "@ZH" zAccent.hex |>.replace "@ZR" zAccent.rgb
    |>.replace "@MH" markHex |>.replace "@AH" antiHex

/-- The stylesheet as an embeddable `<style>` element. -/
def styleTag : Html :=
  el "style" #[] #[.text qecwCss]

/-- Card container shared by all widgets: stylesheet, state bar, body. The
`accent` colors the bar (verdict green/red/amber, or an identity color); `none`
leaves it neutral. -/
def card (children : Array Html) (accent : Option String := none) : Html :=
  let bar := match accent with
    | some c => cls "div" "qecw-bar" #[("style", json% { background: $(c) })]
    | none => cls "div" "qecw-bar"
  cls "div" "qecw-card" #[] #[styleTag, bar, cls "div" "qecw-body" #[] children]

/-- A dim compact header fact ("wt 4", "? 2"); the explanation lives in the
hover tooltip, an optional color marks warnings/verdicts. -/
def headerFact (label : String) (title : String := "")
    (color : Option String := none) : Html :=
  let attrs := #[("title", Json.str title)] ++
    (match color with
     | some c => #[("style", json% { color: $(c) })]
     | none => #[])
  cls "span" "qecw-fact" attrs #[.text label]

/-- Header line: dim name on the left, compact facts on the right. The name is
`Html` so callers can pass an interactive expression (`exprName`). -/
def headerHtml (name : Html) (facts : Array Html) : Html :=
  cls "div" "qecw-head" #[] (#[cls "span" "qecw-name" #[] #[name]] ++ facts)

/-- Interactive expression for card headers: rendered like terms in the goal
view — hover for types and docs, click to go to the definition. -/
def exprName (e : Expr) : MetaM Html := do
  return Html.ofComponent InteractiveCode { fmt := ← Widget.ppExprTagged e } #[]

/-- A compact one-line verdict; the full explanation lives in the tooltip. -/
def verdictLine (color : String) (text : String) (title : String := "") : Html :=
  cls "div" "qecw-verdict"
    #[("title", Json.str title), ("style", json% { color: $(color) })]
    #[.text text]

end QECWidgets
