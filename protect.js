/* © 2025 Ambore.org — All rights reserved. Unauthorized copying is prohibited. */
(function(){
  'use strict';

  /* ── 1. Disable right-click context menu ── */
  document.addEventListener('contextmenu', function(e){
    e.preventDefault();
    return false;
  }, true);

  /* ── 2. Block keyboard shortcuts ── */
  document.addEventListener('keydown', function(e){
    var ctrl = e.ctrlKey || e.metaKey; // Ctrl on Windows/Linux, Cmd on Mac

    // F12 — Open DevTools
    if (e.key === 'F12') { e.preventDefault(); return false; }

    if (ctrl) {
      // Ctrl+Shift+I / J / C — DevTools panels
      if (e.shiftKey && /^[ijcIJC]$/.test(e.key)) { e.preventDefault(); return false; }
      // Ctrl+U — View Source
      if (/^[uU]$/.test(e.key)) { e.preventDefault(); return false; }
      // Ctrl+S — Save Page As
      if (/^[sS]$/.test(e.key)) { e.preventDefault(); return false; }
      // Ctrl+P — Print (reveals source layout)
      if (/^[pP]$/.test(e.key)) { e.preventDefault(); return false; }
    }
  }, true);

  /* ── 3. Block drag-to-copy on images and links ── */
  document.addEventListener('dragstart', function(e){
    if (e.target && (e.target.tagName === 'IMG' || e.target.tagName === 'A')) {
      e.preventDefault();
    }
  });

  /* ── 4. Disable text selection (allow inputs, textareas, contenteditable) ── */
  var style = document.createElement('style');
  style.textContent =
    'body *:not(input):not(textarea):not([contenteditable="true"]){' +
    '-webkit-user-select:none!important;-moz-user-select:none!important;' +
    '-ms-user-select:none!important;user-select:none!important}';
  document.head.appendChild(style);

  /* ── 5. DevTools size detection — show warning overlay ── */
  var _warn = null;
  var _devOpen = false;
  var THRESHOLD = 160;

  function _showWarn() {
    if (_warn) return;
    _warn = document.createElement('div');
    _warn.style.cssText =
      'position:fixed;inset:0;background:rgba(6,6,15,0.97);z-index:2147483647;' +
      'display:flex;align-items:center;justify-content:center;flex-direction:column;' +
      'gap:14px;backdrop-filter:blur(24px);font-family:Inter,sans-serif';
    _warn.innerHTML =
      '<div style="font-size:2.5rem">⛔</div>' +
      '<h2 style="color:#fff;font-size:1.3rem;margin:0;font-weight:800">Developer Tools Detected</h2>' +
      '<p style="color:rgba(255,255,255,0.45);font-size:0.88rem;margin:0;text-align:center;line-height:1.6">' +
      'This content is protected by copyright.<br>Close developer tools to continue.</p>';
    document.body.appendChild(_warn);
  }

  function _hideWarn() {
    if (_warn) { _warn.remove(); _warn = null; }
  }

  function _checkDevTools() {
    var docked = (window.outerWidth - window.innerWidth > THRESHOLD) ||
                 (window.outerHeight - window.innerHeight > THRESHOLD);
    if (docked && !_devOpen) { _devOpen = true;  _showWarn(); }
    if (!docked && _devOpen) { _devOpen = false; _hideWarn(); }
  }

  setInterval(_checkDevTools, 800);

  /* ── 6. Console warning ── */
  setTimeout(function(){
    try {
      console.clear();
      console.log(
        '%c⛔  STOP!',
        'color:#ef4444;font-size:44px;font-weight:900;font-family:monospace'
      );
      console.log(
        '%c This site is protected by copyright.\n © ' +
        new Date().getFullYear() +
        ' Ambore.org — All rights reserved.\n Unauthorized copying or reproduction is strictly prohibited.',
        'color:#e2e8f0;font-size:13px;background:#0d1117;padding:12px 16px;' +
        'border-radius:6px;border-left:3px solid #ef4444;font-family:monospace;line-height:1.7'
      );
    } catch(err) {}
  }, 600);

})();
