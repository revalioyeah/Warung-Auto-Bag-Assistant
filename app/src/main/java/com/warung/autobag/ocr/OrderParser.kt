package com.warung.autobag.ocr

import kotlin.math.abs
import com.warung.autobag.detection.CatalogEntry
import com.warung.autobag.detection.ItemCatalog

/**
 * Satu item pesanan yang berhasil dipisahkan.
 */
data class ParsedOrderItem(
    val name: String,
    val currentQuantity: Int?,
    val requiredQuantity: Int?,
    val rawText: String
)

/**
 * Hasil keseluruhan parsing papan pesanan.
 */
data class OrderParseResult(
    val items: List<ParsedOrderItem>,
    val headerFound: Boolean,
    val message: String,
    // Quantity rows without a paired catalog label indicate that OCR may have
    // missed an item name. Automation must not silently execute a partial order.
    val unmatchedQuantityCount: Int = 0
)

/**
 * Smart Order Parser berbasis koordinat elemen OCR.
 *
 * Alur:
 * 1. Menemukan header PESANAN.
 * 2. Membatasi area pembacaan di sekitar papan pesanan.
 * 3. Membaca kata dan angka menggunakan koordinat Text.Element.
 * 4. Mengenali nama barang, termasuk nama yang terdiri dari beberapa kata.
 * 5. Membatasi pembacaan agar label rak di luar papan tidak ikut terambil.
 * 6. Memasangkan jumlah dengan barang berdasarkan jarak vertikal dan horizontal.
 *
 * Jika data elemen tidak tersedia, parser menggunakan koordinat
 * baris OCR sebagai metode cadangan.
 */
object OrderParser {

    private val quantityPattern = Regex(
        """(?i)(?<!\d)([0-9oOlIQDbgSz]{0,3})\s*[/|!Il1tfl7]\s*([0-9IlQDbgSz]{1,3})(?!\d)"""
    )

    // Padding mengikuti lebar tulisan PESANAN agar tetap proporsional
    // pada screenshot dengan resolusi berbeda. Nilai 1,5 menjaga isi
    // kedua sisi panel tetap terbaca tanpa menjangkau rak kanan.
    private const val BOARD_HORIZONTAL_PADDING_RATIO = 1.2f
    private const val BOARD_VERTICAL_RANGE = 400

    // Jarak vertikal maksimum agar angka tidak dipasangkan
    // dengan barang pada baris yang terlalu jauh.
    private const val MAX_VERTICAL_MATCH_DISTANCE = 85f

    // Bobot jarak: posisi Y lebih penting daripada posisi X,
    // karena jumlah biasanya berada di sisi kanan nama barang.
    private const val VERTICAL_DISTANCE_WEIGHT = 4f
    private const val HORIZONTAL_DISTANCE_WEIGHT = 0.15f

    private data class Box(
        val left: Int,
        val top: Int,
        val right: Int,
        val bottom: Int
    ) {
        val centerX: Float
            get() = (left + right) / 2f

        val centerY: Float
            get() = (top + bottom) / 2f
    }

    private data class ElementSpan(
        val start: Int,
        val endExclusive: Int,
        val box: Box
    )

    private data class LineContent(
        val text: String,
        val spans: List<ElementSpan>,
        val usesElementCoordinates: Boolean,
        val fallbackBox: Box
    )

    private data class TextMatch(
        val name: String,
        val start: Int,
        val endExclusive: Int
    )

    private data class ItemFragment(
        val name: String,
        val box: Box,
        val rawText: String
    )

    private data class QuantityFragment(
        val current: Int?,
        val required: Int,
        val box: Box,
        val rawText: String
    )

    private data class MatchCandidate(
        val itemIndex: Int,
        val quantityIndex: Int,
        val cost: Float
    )

    private data class CompiledCatalogAlias(
        val canonicalName: String,
        val pattern: Regex,
        val aliasLength: Int,
        val normalizedAlias: String
    )

    private val aliasWhitespace = Regex("""\s+""")

    @Volatile
    private var cachedCatalogSnapshot: List<CatalogEntry> = emptyList()

    @Volatile
    private var cachedCompiledCatalogAliases: List<CompiledCatalogAlias> =
        compileCatalogAliases(ItemCatalog.entries)

    private fun aliasesFor(catalogEntries: List<CatalogEntry>): List<CompiledCatalogAlias> {
        val snapshot = catalogEntries.toList()
        if (snapshot == cachedCatalogSnapshot) return cachedCompiledCatalogAliases

        synchronized(this) {
            if (snapshot != cachedCatalogSnapshot) {
                cachedCompiledCatalogAliases = compileCatalogAliases(snapshot)
                cachedCatalogSnapshot = snapshot
            }
            return cachedCompiledCatalogAliases
        }
    }

    private fun compileCatalogAliases(
        catalogEntries: List<CatalogEntry>
    ): List<CompiledCatalogAlias> = catalogEntries
        .flatMap { entry ->
            (listOf(entry.name) + entry.aliases)
                // Pertahankan bentuk seperti "2GB" dan "2 GB".
                .map { it.trim().replace(aliasWhitespace, " ") }
                .distinctBy { it.uppercase() }
                .filter { it.isNotBlank() }
                .map { alias ->
                    val flexiblePattern = alias
                        .split(' ')
                        .joinToString("""\s+""") { Regex.escape(it) }

                    CompiledCatalogAlias(
                        canonicalName = entry.name,
                        pattern = Regex(
                            """(?i)(?<![A-Z0-9])$flexiblePattern(?![A-Z0-9])"""
                        ),
                        aliasLength = normalize(alias).length,
                        normalizedAlias = normalize(alias)
                    )
                }
        }
        .sortedByDescending { it.aliasLength }

    /**
     * Hitung Region of Interest (ROI) dari hasil OCR sebelumnya,
     * sehingga frame berikutnya bisa di-crop terlebih dahulu untuk mempercepat OCR.
     */
    fun calculateBoardRoi(result: OcrResult): android.graphics.Rect? {
        val header = result.lines.firstOrNull { line ->
            normalize(line.text).contains("PESANAN")
        } ?: return null

        val headerWidth = (header.right - header.left).coerceAtLeast(1)
        val horizontalPadding = (headerWidth * BOARD_HORIZONTAL_PADDING_RATIO).toInt()

        val minX = (header.left - horizontalPadding).coerceAtLeast(0)
        val maxX = header.right + horizontalPadding
        val minY = header.top.coerceAtLeast(0)
        val maxY = header.bottom + BOARD_VERTICAL_RANGE

        return android.graphics.Rect(minX, minY, maxX, maxY)
    }

    /**
     * Fungsi utama parsing papan pesanan.
     */
    fun parse(
        result: OcrResult,
        catalogEntries: List<CatalogEntry> = ItemCatalog.entries
    ): OrderParseResult {
        val compiledAliases = aliasesFor(catalogEntries)

        // 1. Cari header PESANAN.
        val header = result.lines.firstOrNull { line ->
            normalize(line.text).contains("PESANAN")
        } ?: return OrderParseResult(
            items = emptyList(),
            headerFound = false,
            message = "Papan PESANAN belum ditemukan."
        )

        // 2. Batasi area OCR di sekitar header.
        val headerWidth = (header.right - header.left).coerceAtLeast(1)
        val horizontalPadding =
            (headerWidth * BOARD_HORIZONTAL_PADDING_RATIO).toInt()

        val minX = header.left - horizontalPadding
        val maxX = header.right + horizontalPadding
        val maxY = header.bottom + BOARD_VERTICAL_RANGE

        val boardLines = result.lines.filter { line ->

            val intersectsHorizontalArea =
                line.right >= minX && line.left <= maxX

            intersectsHorizontalArea &&
                line.top > header.bottom &&
                line.top <= maxY &&
                line.text.isNotBlank()
        }

        if (boardLines.isEmpty()) {
            return OrderParseResult(
                items = emptyList(),
                headerFound = true,
                message = "Header ditemukan, tetapi isi papan belum terbaca."
            )
        }

        // 3. Ambil fragmen nama barang dan jumlah.
        // Posisi dihitung dari Text.Element apabila tersedia.
        val rawItems = mutableListOf<Pair<String, Box>>()
        val rawQuantities =
            mutableListOf<Triple<Int?, Int, Pair<Box, String>>>()

        for (line in boardLines) {

            val content = buildLineContent(line)
            if (content.text.isBlank()) continue

            // Cari nama barang pada teks gabungan elemen.
            val itemMatches = findCatalogMatches(content.text, compiledAliases)

            for (match in itemMatches) {

                val box = boundsForRange(
                    content = content,
                    start = match.start,
                    endExclusive = match.endExclusive
                )

                rawItems.add(
                    match.name to box
                )
            }

            // Cari angka jumlah, misalnya 0/1, O/2, atau 0|3.
            for (match in quantityPattern.findAll(content.text)) {

                // OCR terkadang membaca angka 0 sebagai huruf O.
                // Jumlah berjalan juga dapat berupa 1, 2, dan seterusnya.
                val currentText = normalizeDigits(match.groupValues[1])

                val current = currentText.toIntOrNull()
                    // OCR kadang menghilangkan pembilang (membaca "/5" bukan "0/5").
                    // Pembilang yang tidak terbaca dianggap 0 agar pesanan tetap bisa
                    // diproses; papan pesanan biasanya mulai dari 0.
                    ?: 0

                val requiredText = normalizeDigits(match.groupValues[2])
                val required = requiredText.toIntOrNull()

                // Pembilang boleh tidak terbaca OCR.
                // Penyebut tetap harus berhasil dikenali.
                if (required != null) {

                    val box = boundsForRange(
                        content = content,
                        start = match.range.first,
                        endExclusive = match.range.last + 1
                    )

                    rawQuantities.add(
                        Triple(
                            current,
                            required,
                            box to match.value
                        )
                    )
                }
            }
        }

        if (rawItems.isEmpty()) {
            return OrderParseResult(
                items = emptyList(),
                headerFound = true,
                message = "Papan ditemukan, tetapi nama barang belum berhasil dikenali.",
                unmatchedQuantityCount = rawQuantities.size
            )
        }

        // 4. Simpan posisi nama barang dan jumlah secara terpisah.
        // Parser tidak memaksakan pembagian kolom karena beberapa papan
        // menampilkan satu kolom, sementara papan lain menampilkan dua.
        val itemFragments = rawItems.map { (name, box) ->
            ItemFragment(
                name = name,
                box = box,
                rawText = name
            )
        }.distinctBy { item ->
            listOf(
                item.name,
                (item.box.centerX / 20f).toInt(),
                (item.box.centerY / 20f).toInt()
            )
        }

        val quantityFragments = rawQuantities.map { raw ->
            QuantityFragment(
                current = raw.first,
                required = raw.second,
                box = raw.third.first,
                rawText = raw.third.second
            )
        }.distinctBy { quantity ->
            listOf(
                quantity.current,
                quantity.required,
                (quantity.box.centerX / 20f).toInt(),
                (quantity.box.centerY / 20f).toInt()
            )
        }

        // 5. Pasangkan jumlah dengan barang berdasarkan kedekatan posisi.
        val assignments = matchQuantities(
            items = itemFragments,
            quantities = quantityFragments
        )

        // 6. Susun hasil dari atas ke bawah, lalu kiri ke kanan.
        // HANYA masukkan nama barang yang memiliki pasangan jumlah pesanan.
        // Ini mencegah label stok di rak (mis. Rengginang) dianggap sebagai
        // pesanan hanya karena ikut terbaca di area OCR yang luas.
        val parsedItems = itemFragments.withIndex()
            .sortedWith(
                compareBy<IndexedValue<ItemFragment>> { it.value.box.centerY }
                    .thenBy { it.value.box.centerX }
            )
            .mapNotNull { indexedItem ->
                val item = indexedItem.value
                val quantityIndex = assignments[indexedItem.index]
                    ?: return@mapNotNull null
                val quantity = quantityFragments.getOrNull(quantityIndex)
                    ?: return@mapNotNull null

                // Pastikan requiredQuantity valid (bukan null atau zero yang tidak masuk akal)
                if (quantity.required <= 0) return@mapNotNull null

                ParsedOrderItem(
                    name = item.name,
                    currentQuantity = quantity.current,
                    requiredQuantity = quantity.required,
                    rawText = "${item.rawText} | ${quantity.rawText}"
                )
            }

        val ignoredUnpairedLabels = itemFragments.size - parsedItems.size
        val matchedQuantityIndices = assignments.values.toSet()
        val unmatchedQuantityCount =
            (quantityFragments.size - matchedQuantityIndices.size).coerceAtLeast(0)

        return OrderParseResult(
            items = parsedItems,
            headerFound = true,
            unmatchedQuantityCount = unmatchedQuantityCount,
            message = when {
                parsedItems.isEmpty() ->
                    "Papan ditemukan, tetapi belum ada nama barang yang cocok dengan jumlah pesanan."
                ignoredUnpairedLabels > 0 ->
                    "${parsedItems.size} item pesanan berhasil dipisahkan; $ignoredUnpairedLabels label tanpa jumlah pesanan diabaikan."
                else ->
                    "${parsedItems.size} item pesanan berhasil dipisahkan."
            }
        )
    }

    /**
     * Membentuk teks satu baris dari elemen OCR.
     *
     * Setiap elemen menyimpan rentang karakter dan bounding box.
     * Dengan demikian, posisi nama barang dan angka dapat dihitung
     * secara terpisah walaupun berada dalam satu Text.Line.
     */
    private fun buildLineContent(line: RecognizedLine): LineContent {

        val validElements = line.elements
            .filter { it.text.isNotBlank() }
            .sortedBy { it.left }

        if (validElements.isNotEmpty()) {

            val builder = StringBuilder()
            val spans = mutableListOf<ElementSpan>()

            for (element in validElements) {

                if (builder.isNotEmpty()) {
                    builder.append(' ')
                }

                val start = builder.length
                builder.append(element.text)
                val end = builder.length

                spans.add(
                    ElementSpan(
                        start = start,
                        endExclusive = end,
                        box = Box(
                            left = element.left,
                            top = element.top,
                            right = element.right,
                            bottom = element.bottom
                        )
                    )
                )
            }

            return LineContent(
                text = builder.toString(),
                spans = spans,
                usesElementCoordinates = true,
                fallbackBox = Box(
                    line.left,
                    line.top,
                    line.right,
                    line.bottom
                )
            )
        }

        // Metode cadangan untuk data OCR lama yang belum memiliki
        // koordinat per elemen.
        return LineContent(
            text = line.text,
            spans = emptyList(),
            usesElementCoordinates = false,
            fallbackBox = Box(
                line.left,
                line.top,
                line.right,
                line.bottom
            )
        )
    }

    /**
     * Mengambil bounding box untuk rentang teks tertentu.
     *
     * Jika koordinat elemen tersedia, gunakan gabungan bounding box
     * elemen yang bersinggungan dengan rentang teks.
     *
     * Jika tidak tersedia, estimasikan posisi karakter di dalam
     * bounding box baris OCR.
     */
    private fun boundsForRange(
        content: LineContent,
        start: Int,
        endExclusive: Int
    ): Box {

        if (content.usesElementCoordinates) {

            val overlappingSpans = content.spans.filter { span ->
                span.start < endExclusive &&
                    span.endExclusive > start
            }

            if (overlappingSpans.isNotEmpty()) {
                return Box(
                    left = overlappingSpans.minOf { it.box.left },
                    top = overlappingSpans.minOf { it.box.top },
                    right = overlappingSpans.maxOf { it.box.right },
                    bottom = overlappingSpans.maxOf { it.box.bottom }
                )
            }
        }

        val textLength = content.text.length.coerceAtLeast(1)
        val box = content.fallbackBox
        val width = (box.right - box.left).coerceAtLeast(1)

        val safeStart = start.coerceIn(0, textLength)
        val safeEnd = endExclusive.coerceIn(safeStart, textLength)

        val estimatedLeft = box.left +
            (width * safeStart.toFloat() / textLength).toInt()

        val estimatedRight = box.left +
            (width * safeEnd.toFloat() / textLength).toInt()

        return Box(
            left = estimatedLeft,
            top = box.top,
            right = estimatedRight.coerceAtLeast(estimatedLeft + 1),
            bottom = box.bottom
        )
    }

    /**
     * Mencari semua nama barang dalam teks.
     *
     * Contoh:
     * "Makanan kucing 0/1"
     *
     * Nama barang yang dihasilkan:
     * "Makanan kucing"
     */
    private fun findCatalogMatches(
        text: String,
        compiledAliases: List<CompiledCatalogAlias>
    ): List<TextMatch> {

        val found = mutableListOf<TextMatch>()

        for (alias in compiledAliases) {
            for (match in alias.pattern.findAll(text)) {

                val candidate = TextMatch(
                    name = alias.canonicalName,
                    start = match.range.first,
                    endExclusive = match.range.last + 1
                )

                val overlaps = found.any { existing ->
                    candidate.start < existing.endExclusive &&
                        candidate.endExclusive > existing.start
                }

                if (!overlaps) {
                    found.add(candidate)
                }
            }
        }

        if (found.isNotEmpty()) {
            return found.sortedBy { it.start }
        }

        // OCR can confuse one or two characters in longer product labels.
        // Use a conservative fuzzy fallback only when no exact alias matched.
        val fuzzy = findFuzzyCatalogMatch(text, compiledAliases)
        return if (fuzzy != null) listOf(fuzzy) else emptyList()
    }

    private data class FuzzyCandidate(
        val match: TextMatch,
        val distance: Int,
        val aliasLength: Int
    )

    private fun findFuzzyCatalogMatch(
        text: String,
        aliases: List<CompiledCatalogAlias>
    ): TextMatch? {
        val normalizedChars = mutableListOf<Char>()
        val originalIndices = mutableListOf<Int>()
        text.forEachIndexed { index, char ->
            if (char.isLetterOrDigit()) {
                normalizedChars += char.uppercaseChar()
                originalIndices += index
            }
        }
        if (normalizedChars.isEmpty()) return null

        val source = normalizedChars.joinToString("")
        val candidates = mutableListOf<FuzzyCandidate>()

        for (alias in aliases) {
            val target = alias.normalizedAlias
            val maxDistance = when {
                target.length < 5 -> 0
                target.length <= 11 -> 1
                else -> 2
            }
            if (maxDistance == 0 || target.length < 5) continue

            val minLength = (target.length - maxDistance).coerceAtLeast(1)
            val maxLength = target.length + maxDistance
            for (start in source.indices) {
                if (source[start] != target.first()) continue
                for (length in minLength..maxLength) {
                    val end = start + length
                    if (end > source.length) continue
                    val candidate = source.substring(start, end)
                    val distance = editDistanceAtMost(target, candidate, maxDistance)
                    if (distance > maxDistance) continue

                    val originalStart = originalIndices[start]
                    val originalEnd = originalIndices[end - 1] + 1
                    val leftBoundaryIsValid =
                        originalStart == 0 || !text[originalStart - 1].isLetterOrDigit()
                    val rightBoundaryIsValid =
                        originalEnd >= text.length || !text[originalEnd].isLetterOrDigit()
                    if (!leftBoundaryIsValid || !rightBoundaryIsValid) continue

                    candidates += FuzzyCandidate(
                        match = TextMatch(
                            name = alias.canonicalName,
                            start = originalStart,
                            endExclusive = originalEnd
                        ),
                        distance = distance,
                        aliasLength = target.length
                    )
                }
            }
        }

        if (candidates.isEmpty()) return null
        val ranked = candidates.sortedWith(
            compareBy<FuzzyCandidate> { it.distance }
                .thenByDescending { it.aliasLength }
        )
        val best = ranked.first()
        val tiedNames = ranked
            .filter { it.distance == best.distance && it.aliasLength == best.aliasLength }
            .map { it.match.name }
            .distinct()
        if (tiedNames.size > 1) return null
        return best.match
    }

    private fun editDistanceAtMost(left: String, right: String, limit: Int): Int {
        if (kotlin.math.abs(left.length - right.length) > limit) return limit + 1
        var previous = IntArray(right.length + 1) { it }
        for (i in left.indices) {
            val current = IntArray(right.length + 1)
            current[0] = i + 1
            var rowMinimum = current[0]
            for (j in right.indices) {
                val cost = if (left[i] == right[j]) 0 else 1
                current[j + 1] = minOf(
                    current[j] + 1,
                    previous[j + 1] + 1,
                    previous[j] + cost
                )
                rowMinimum = minOf(rowMinimum, current[j + 1])
            }
            if (rowMinimum > limit) return limit + 1
            previous = current
        }
        return previous[right.length]
    }

    /**
     * Memasangkan jumlah dan barang dengan metode nearest-neighbor
     * satu-ke-satu. Jarak vertikal menjadi prioritas; jarak horizontal
     * membantu memilih item yang tepat pada papan dua kolom.
     *
     * Setiap angka hanya dapat digunakan satu kali.
     */
    private fun matchQuantities(
        items: List<ItemFragment>,
        quantities: List<QuantityFragment>
    ): Map<Int, Int> {

        val candidates = mutableListOf<MatchCandidate>()

        for ((itemIndex, item) in items.withIndex()) {

            for ((quantityIndex, quantity) in quantities.withIndex()) {

                // Jangan wajibkan kolom yang sama. Pada papan satu kolom,
                // nama barang berada di kiri dan jumlah berada di kanan.
                // Pembatasan kolom lama membuat pasangan seperti ini hilang.

                val verticalDistance = abs(
                    item.box.centerY - quantity.box.centerY
                )

                if (verticalDistance > MAX_VERTICAL_MATCH_DISTANCE) {
                    continue
                }

                val horizontalDistance = abs(
                    item.box.centerX - quantity.box.centerX
                )

                val cost =
                    verticalDistance * VERTICAL_DISTANCE_WEIGHT +
                        horizontalDistance * HORIZONTAL_DISTANCE_WEIGHT

                candidates.add(
                    MatchCandidate(
                        itemIndex = itemIndex,
                        quantityIndex = quantityIndex,
                        cost = cost
                    )
                )
            }
        }

        val assignments = mutableMapOf<Int, Int>()
        val usedQuantities = mutableSetOf<Int>()

        // Pasangan dengan jarak terdekat diproses terlebih dahulu.
        for (candidate in candidates.sortedBy { it.cost }) {

            if (candidate.itemIndex in assignments) {
                continue
            }

            if (candidate.quantityIndex in usedQuantities) {
                continue
            }

            assignments[candidate.itemIndex] =
                candidate.quantityIndex

            usedQuantities.add(candidate.quantityIndex)
        }

        return assignments
    }

    /**
     * Normalisasi karakter yang sering dibaca OCR sebagai angka.
     */
    private fun normalizeDigits(text: String): String {
        return text
            .replace('o', '0', ignoreCase = true)
            .replace('q', '0', ignoreCase = true)
            .replace('d', '0', ignoreCase = true)
            .replace('?', '0', ignoreCase = true)
            .replace('a', '0', ignoreCase = true)
            .replace('i', '1', ignoreCase = true)
            .replace('l', '1', ignoreCase = true)
            .replace('|', '1', ignoreCase = true)
            .replace('I', '1', ignoreCase = true)
            .replace('t', '1', ignoreCase = true)
            .replace('f', '1', ignoreCase = true)
            .replace('7', '1', ignoreCase = true)
            .replace('z', '2', ignoreCase = true)
            .replace('s', '5', ignoreCase = true)
            .replace('g', '6', ignoreCase = true)
            .replace('b', '8', ignoreCase = true)
    }

    /**
     * Normalisasi teks untuk pencarian header dan katalog.
     */
    private fun normalize(text: String): String {
        return text
            .uppercase()
            .replace(Regex("""[^A-Z0-9]"""), "")
    }
}
