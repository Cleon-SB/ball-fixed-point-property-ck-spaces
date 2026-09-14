document.addEventListener('click', async event => {
  const button = event.target.closest('button[data-copy]');
  if (!button) return;
  const target = document.getElementById(button.dataset.copy);
  if (!target) return;
  const status = document.getElementById('copy-status');
  try {
    await navigator.clipboard.writeText(target.textContent);
    button.textContent = 'Copied';
    status.textContent = 'Copied to clipboard.';
    setTimeout(() => { button.textContent = 'Copy'; status.textContent = ''; }, 2000);
  } catch {
    const selection = window.getSelection();
    const range = document.createRange();
    range.selectNodeContents(target);
    selection.removeAllRanges();
    selection.addRange(range);
    status.textContent = 'Text selected. Use Ctrl+C or Command+C to copy.';
    setTimeout(() => { status.textContent = ''; }, 5000);
  }
});
