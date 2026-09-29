$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath $PSScriptRoot
lake env leanchecker --fresh --verbose Certificate
if ($LASTEXITCODE -ne 0) { throw 'Fresh kernel replay failed.' }
'PASS: fresh kernel replay.'
