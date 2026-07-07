$ErrorActionPreference = "Stop"

cd "C:\apps\Qld Only Iso"

$stamp = Get-Date -Format "yyyyMMdd_HHmmss"

if (Test-Path ".\places.csv") {
  Copy-Item ".\places.csv" ".\places_backup_before_connected_roadpoints_$stamp.csv" -Force
}

py .\build_places_from_qld_localities_connected_roadpoints.py `
  --graph .\qld_drive.graphml `
  --existing .\places.csv `
  --manual-connectors .\manual_graph_connectors.csv `
  --output .\places_all_qld_localities_connected_roadpoints.csv

Write-Host "`n=== New connected-roadpoint places file count ==="
Import-Csv .\places_all_qld_localities_connected_roadpoints.csv | Measure-Object

Write-Host "`n=== Point method counts ==="
Import-Csv .\places_all_qld_localities_connected_roadpoints.csv |
  Group-Object point_method |
  Sort-Object Name |
  Select-Object Name,Count |
  Format-Table -AutoSize

Write-Host "`nReview .\places_all_qld_localities_connected_roadpoints.csv before replacing places.csv."
Write-Host "When happy, run:"
Write-Host "  Copy-Item .\places_all_qld_localities_connected_roadpoints.csv .\places.csv -Force"
