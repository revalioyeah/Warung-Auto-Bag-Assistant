package com.warung.autobag.detection

import com.warung.autobag.ocr.OcrResult
import com.warung.autobag.ocr.OrderParser
import com.warung.autobag.ocr.ParsedOrderItem
import com.warung.autobag.ocr.RecognizedElement
import com.warung.autobag.ocr.RecognizedLine

fun main() {
    var checks = 0
    fun expect(condition: Boolean, label: String) {
        check(condition) { label }
        checks++
    }

    val imageWidth = 2340
    val imageHeight = 1080

    // Test case 1: "Kopi susu" - Right Shelf
    val kopiSusuLabel = RecognizedLine(
        text = "Kopi ssu", // Typo for "Kopi susu"
        left = 1300, top = 410, right = 1450, bottom = 438,
        elements = listOf(
            RecognizedElement("Kopi", 1300, 410, 1370, 438),
            RecognizedElement("ssu", 1375, 410, 1450, 438)
        )
    )
    val kopiSusuOrder = ParsedOrderItem(name = "Kopi susu", currentQuantity = 0, requiredQuantity = 1, rawText = "Kopi ssu 0I1")
    val kopiSusuDetection = SmartItemDetector.detect(
        ocrResult = OcrResult(fullText = kopiSusuLabel.text, lines = listOf(kopiSusuLabel)),
        orders = listOf(kopiSusuOrder),
        imageWidth = imageWidth,
        imageHeight = imageHeight,
        catalogEntries = BattleItemCatalog.entries
    )
    expect(kopiSusuDetection.detections.size == 1, "Battle: Kopi susu detected with typo")
    val ksTarget = kopiSusuDetection.detections.first()
    expect(ksTarget.itemName == "Kopi susu", "Battle: Kopi susu canonical name correct")
    expect(ksTarget.shelfRegion == "RIGHT_SHELF", "Battle: Kopi susu right shelf region correct")
    expect(ksTarget.targetX / imageWidth.toFloat() in 0.5f..0.98f, "Battle: Kopi susu target X in right shelf region")

    // Test case 2: "Mie rebus" - Left Shelf
    val mieRebusLabel = RecognizedLine(
        text = "Mie rebs", // Typo for "Mie rebus"
        left = 420, top = 410, right = 550, bottom = 438,
        elements = listOf(
            RecognizedElement("Mie", 420, 410, 460, 438),
            RecognizedElement("rebs", 465, 410, 550, 438)
        )
    )
    val mieRebusOrder = ParsedOrderItem(name = "Mie rebus", currentQuantity = 0, requiredQuantity = 1, rawText = "Mie rebs 0I1")
    val mieRebusDetection = SmartItemDetector.detect(
        ocrResult = OcrResult(fullText = mieRebusLabel.text, lines = listOf(mieRebusLabel)),
        orders = listOf(mieRebusOrder),
        imageWidth = imageWidth,
        imageHeight = imageHeight,
        catalogEntries = BattleItemCatalog.entries
    )
    expect(mieRebusDetection.detections.size == 1, "Battle: Mie rebus detected with typo")
    val mrTarget = mieRebusDetection.detections.first()
    expect(mrTarget.itemName == "Mie rebus", "Battle: Mie rebus canonical name correct")
    expect(mrTarget.shelfRegion == "LEFT_SHELF", "Battle: Mie rebus left shelf region correct")
    expect(mrTarget.targetX / imageWidth.toFloat() in 0.02f..0.45f, "Battle: Mie rebus target X in left shelf region")

    // Test case 3: "Teh celup" - Left Shelf, out of bounds
    val tehCelupOutOfBoundsLabel = RecognizedLine(
        text = "Teh celp", // Typo for "Teh celup"
        left = 420, top = 100, right = 550, bottom = 128, // Too high on screen
        elements = listOf(
            RecognizedElement("Teh", 420, 100, 460, 128),
            RecognizedElement("celp", 465, 100, 550, 128)
        )
    )
    val tehCelupOrder = ParsedOrderItem(name = "Teh celup", currentQuantity = 0, requiredQuantity = 1, rawText = "Teh celp 0I1")
    val tehCelupOutOfBoundsDetection = SmartItemDetector.detect(
        ocrResult = OcrResult(fullText = tehCelupOutOfBoundsLabel.text, lines = listOf(tehCelupOutOfBoundsLabel)),
        orders = listOf(tehCelupOrder),
        imageWidth = imageWidth,
        imageHeight = imageHeight,
        catalogEntries = BattleItemCatalog.entries
    )
    expect(tehCelupOutOfBoundsDetection.detections.isEmpty(), "Battle: Teh celup out of bounds is rejected")


    println("BattleItemDetectionRegression: $checks checks passed")
}
