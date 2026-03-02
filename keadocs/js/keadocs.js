/**
 * keadocs.js — progressive enhancement for kea documentation
 *
 * Three responsibilities:
 *   1. Theme toggle (dark mode)
 *   2. Effect expand panels
 *   3. Search overlay (Phase B — stubbed)
 *
 * The page is fully functional without this script.
 * Theme respects prefers-color-scheme via CSS. Effect expand panels
 * are hidden by default. Search falls back to browser find.
 */

;(function () {
  'use strict'

  // ================================================================
  // 1. Theme toggle
  // ================================================================

  var STORAGE_KEY = 'kd-theme'

  function getStoredTheme () {
    try { return localStorage.getItem(STORAGE_KEY) } catch (e) { return null }
  }

  function setStoredTheme (theme) {
    try { localStorage.setItem(STORAGE_KEY, theme) } catch (e) { /* noop */ }
  }

  function getEffectiveTheme () {
    var stored = getStoredTheme()
    if (stored === 'dark' || stored === 'light') return stored
    return window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light'
  }

  function applyTheme (theme) {
    document.documentElement.setAttribute('data-theme', theme)
    updateToggleButtons(theme)
  }

  function updateToggleButtons (theme) {
    var buttons = document.querySelectorAll('.kd-theme-toggle')
    for (var i = 0; i < buttons.length; i++) {
      buttons[i].textContent = theme === 'dark' ? '●' : '○'
      buttons[i].setAttribute('aria-label',
        theme === 'dark' ? 'Switch to light mode' : 'Switch to dark mode')
    }
  }

  function toggleTheme () {
    var current = getEffectiveTheme()
    var next = current === 'dark' ? 'light' : 'dark'
    setStoredTheme(next)
    applyTheme(next)
  }

  // Apply stored theme immediately
  var stored = getStoredTheme()
  if (stored) applyTheme(stored)
  else updateToggleButtons(getEffectiveTheme())

  // Bind toggle buttons via delegation
  document.addEventListener('click', function (e) {
    if (e.target.closest('.kd-theme-toggle')) {
      e.preventDefault()
      toggleTheme()
    }
  })

  // Listen for system theme changes when no stored preference
  try {
    window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', function (e) {
      if (!getStoredTheme()) {
        updateToggleButtons(e.matches ? 'dark' : 'light')
      }
    })
  } catch (e) { /* older browsers */ }

  // ================================================================
  // 2. Effect expand panels
  // ================================================================

  document.addEventListener('click', function (e) {
    var trigger = e.target.closest('.kd-effect-trigger')
    if (!trigger) return

    e.preventDefault()

    var sig = trigger.closest('.kd-sig, .kd-effect-decl')
    if (!sig) return

    var panel = sig.querySelector('.kd-expand')
    if (!panel) return

    panel.classList.toggle('kd-expand--visible')
    trigger.setAttribute('aria-expanded',
      panel.classList.contains('kd-expand--visible') ? 'true' : 'false')
  })

  // ================================================================
  // 3. Search (Phase B — stub)
  // ================================================================

  document.addEventListener('keydown', function (e) {
    var isMod = navigator.platform.indexOf('Mac') > -1 ? e.metaKey : e.ctrlKey
    if (isMod && e.key === 'k') {
      // Phase B: open search overlay
      // e.preventDefault()
    }
  })

})()
