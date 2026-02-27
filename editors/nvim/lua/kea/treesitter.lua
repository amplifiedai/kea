local M = {}

function M.setup()
  local ok, parsers = pcall(require, "nvim-treesitter.parsers")
  if not ok then
    return
  end

  local parser_config = parsers.get_parser_configs()

  -- Locate tree-sitter-kea relative to this plugin (../../tree-sitter-kea).
  local this_file = debug.getinfo(1, "S").source:sub(2)
  local this_dir = vim.fn.fnamemodify(this_file, ":p:h")
  local repo_root = vim.fn.fnamemodify(this_dir, ":h:h:h:h")
  local local_grammar = repo_root .. "/tree-sitter-kea"

  local url
  if vim.fn.isdirectory(local_grammar) == 1 then
    url = local_grammar
  else
    url = "https://github.com/kea-lang/tree-sitter-kea"
  end

  if not parser_config.kea then
    parser_config.kea = {
      install_info = {
        url = url,
        files = { "src/parser.c" },
        branch = "main",
        generate_requires_npm = false,
        requires_generate_from_grammar = false,
      },
      filetype = "kea",
    }
  end
end

return M
