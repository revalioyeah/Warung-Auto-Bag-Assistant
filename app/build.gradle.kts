
plugins {
    id("com.android.application")
    id("org.jetbrains.kotlin.android")
}

android {
    namespace = "com.warung.autobag"
    compileSdk = 33

    defaultConfig {
        applicationId = "com.warung.autobag"
        minSdk = 26
        targetSdk = 33
        versionCode = 17
        versionName = "0.3.17-offline-fast-order"
    }

    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_17
        targetCompatibility = JavaVersion.VERSION_17
    }

    kotlinOptions {
        jvmTarget = "17"
    }

    // Release keys are supplied by the owner; never bundle a private key in source.
    val releaseStore = System.getenv("WARUNG_KEYSTORE_PATH")
    if (!releaseStore.isNullOrBlank()) {
        signingConfigs.create("ownerRelease") {
            storeFile = file(releaseStore)
            storePassword = System.getenv("WARUNG_STORE_PASSWORD")
            keyAlias = System.getenv("WARUNG_KEY_ALIAS")
            keyPassword = System.getenv("WARUNG_KEY_PASSWORD")
        }
    }
    buildTypes {
        getByName("release") {
            isDebuggable = false
            isMinifyEnabled = false
            if (!releaseStore.isNullOrBlank()) {
                signingConfig = signingConfigs.getByName("ownerRelease")
            }
        }
    }

    testOptions {
        unitTests {
            isIncludeAndroidResources = true
        }
    }

    sourceSets {
        // Tes regresi berada di direktori tests/ di tingkat root.
        getByName("test") {
            kotlin.srcDir(rootProject.file("tests"))
        }
    }
}

dependencies {

    // Google ML Kit Text Recognition v2
    // Bundled Latin OCR model
    implementation("com.google.mlkit:text-recognition:16.0.1")

    testImplementation(kotlin("test"))
    testImplementation(kotlin("test-junit"))
}

