/* Ambore Theme Manager — always dark mode */
(function () {
  // Always dark — clear any old saved light preference
  localStorage.removeItem('ambore_theme');
  document.documentElement.setAttribute('data-theme', 'dark');
})();
