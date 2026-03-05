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

  /* ── 5. Console warning ── */
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
