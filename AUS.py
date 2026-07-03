from __future__ import annotations

import csv
import io
import json
import math
import sys
import textwrap
import urllib.error
import urllib.request
import zipfile
from dataclasses import dataclass
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse


GEONAMES_AU_ZIP_URL = "https://download.geonames.org/export/dump/AU.zip"
GEONAMES_TXT_NAME = "AU.txt"
AU_STATES_MAP_URL = "https://www.freeworldmaps.net/australia/australia-map.jpg"
AU_STATES_MAP_NAME = "australia_states_map.jpg"
CITIES_PER_TERRITORY = 15
INDEPENDENT_FEATURE_CODES = {"PPL", "PPLA", "PPLA2", "PPLA3", "PPLA4", "PPLC"}
SEPARATION_STEPS_KM = (30.0, 20.0, 10.0, 0.0)

# GeoNames admin1 numeric codes for Australia.
ADMIN1_TO_STATE = {
	"01": "Australian Capital Territory",
	"02": "New South Wales",
	"03": "Northern Territory",
	"04": "Queensland",
	"05": "South Australia",
	"06": "Tasmania",
	"07": "Victoria",
	"08": "Western Australia",
}

STATE_ALIASES = {
	"act": "Australian Capital Territory",
	"australian capital territory": "Australian Capital Territory",
	"nsw": "New South Wales",
	"new south wales": "New South Wales",
	"nt": "Northern Territory",
	"northern territory": "Northern Territory",
	"qld": "Queensland",
	"queensland": "Queensland",
	"sa": "South Australia",
	"south australia": "South Australia",
	"tas": "Tasmania",
	"tasmania": "Tasmania",
	"vic": "Victoria",
	"victoria": "Victoria",
	"wa": "Western Australia",
	"western australia": "Western Australia",
}

DIRECTION_ALIASES = {
	"n": "N",
	"north": "N",
	"ne": "NE",
	"northeast": "NE",
	"north-east": "NE",
	"e": "E",
	"east": "E",
	"se": "SE",
	"southeast": "SE",
	"south-east": "SE",
	"s": "S",
	"south": "S",
	"sw": "SW",
	"southwest": "SW",
	"south-west": "SW",
	"w": "W",
	"west": "W",
	"nw": "NW",
	"northwest": "NW",
	"north-west": "NW",
}


HTML_PAGE = """<!doctype html>
	<html lang="en">
	<head>
		<meta charset="UTF-8" />
		<meta name="viewport" content="width=device-width, initial-scale=1.0" />
		<title>Australian Geography Quiz</title>
		<style>
			:root {
				--bg: #f2f2f2;
				--panel: #ffffff;
				--text: #1f1f1f;
				--line: #d3d3d3;
				--button: #2e6f95;
				--button-text: #ffffff;
				--ok-bg: #e9f6ed;
				--ok-text: #205c35;
				--bad-bg: #fdeeee;
				--bad-text: #8e1f1f;
			}

			* { box-sizing: border-box; }

			body {
				margin: 0;
				font-family: "Segoe UI", Tahoma, sans-serif;
				color: var(--text);
				background: var(--bg);
			}

			main {
				max-width: 920px;
				margin: 20px auto;
				padding: 16px;
			}

			.panel {
				background: var(--panel);
				border: 1px solid var(--line);
				padding: 16px;
				margin-bottom: 14px;
			}

			h1 {
				margin: 0 0 8px;
				font-size: 1.8rem;
			}

			p { margin: 6px 0; }

			.row {
				display: grid;
				gap: 10px;
			}

			.row.inline {
				grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));
				align-items: end;
			}

			label {
				display: block;
				font-weight: 600;
				margin-bottom: 4px;
			}

			input, select, button {
				width: 100%;
				padding: 10px;
				font-size: 1rem;
				border: 1px solid var(--line);
				background: #fff;
			}

			button {
				background: var(--button);
				color: var(--button-text);
				cursor: pointer;
				border: none;
			}

			button:disabled {
				opacity: 0.6;
				cursor: not-allowed;
			}

			.meta {
				display: flex;
				justify-content: space-between;
				gap: 8px;
				font-weight: 600;
				margin-bottom: 8px;
			}

			#feedback {
				padding: 10px;
				border: 1px solid var(--line);
				display: none;
			}

			#feedback.show {
				display: block;
			}

			.feedback-line {
				padding: 6px 8px;
				border: 1px solid var(--line);
				margin-bottom: 6px;
			}

			.feedback-line:last-child {
				margin-bottom: 0;
			}

			.feedback-line.ok {
				background: var(--ok-bg);
				color: var(--ok-text);
			}

			.feedback-line.bad {
				background: var(--bad-bg);
				color: var(--bad-text);
			}

			#mapArea {
				display: none;
			}

			#map {
				height: 320px;
				border: 1px solid var(--line);
				margin-top: 8px;
				background: #eef5fb;
				overflow: hidden;
				position: relative;
			}

			.map-note {
				display: inline-block;
				margin: 8px;
				font-size: 0.8rem;
				background: #ffffff;
				border: 1px solid var(--line);
				padding: 2px 6px;
			}

			#map .map-canvas {
				position: absolute;
				left: 0;
				right: 0;
				top: 36px;
				bottom: 0;
			}

			#map .marker-layer {
				position: absolute;
				left: 0;
				right: 0;
				top: 0;
				bottom: 0;
				pointer-events: none;
			}

			#map .map-image {
				width: 100%;
				height: 100%;
				object-fit: contain;
				display: block;
			}

			.city-dot {
				position: absolute;
				width: 10px;
				height: 10px;
				border-radius: 50%;
				transform: translate(-50%, -50%);
				border: 1px solid #1f1f1f;
			}

			.city-dot.previous {
				fill: #7a7a7a;
				background: #7a7a7a;
			}

			.city-dot.current {
				background: #2e6f95;
			}

			.city-label {
				position: absolute;
				font-size: 11px;
				color: #1f1f1f;
				background: rgba(255, 255, 255, 0.92);
				border: 1px solid #cfd8df;
				padding: 1px 4px;
				border-radius: 3px;
				transform: translate(7px, -16px);
				white-space: nowrap;
			}

			.hidden { display: none; }

			@media (max-width: 640px) {
				main { margin: 8px auto; padding: 10px; }
				#map { height: 260px; }
			}
		</style>
	</head>
	<body>
		<main>
			<section class="panel">
				<h1>impossible AUS geography</h1>
				<p>Guess state and the direction from the previous city.</p>
				<p>Good luck with this shit</p>
				<p>Australian Capital Territory,New South Wales,
	            Northern Territory,Queensland,South Australia,
				Tasmania,Victoria,Western Australia. ACT, NSW, NT, QLD, SA, TAS, VIC, WA</p>
			</section>

			<section id="setup" class="panel row">
				<div class="row inline">
					<div>
						<label for="questionCount">Number of Questions</label>
						<input id="questionCount" type="number" min="1" value="20" />
					</div>
					<div>
						<button id="startBtn">Start Quiz</button>
					</div>
				</div>
				<p>Directions: N, NE, E, SE, S, SW, W, NW</p>
			</section>

			<section id="quiz" class="panel hidden">
				<div class="meta">
					<span id="progress"></span>
					<span id="score"></span>
				</div>

				<h2 id="cityName"></h2>
				<p id="previousCity"></p>

				<div class="row inline">
					<div>
						<label for="stateInput">State or Territory</label>
						<input id="stateInput" type="text" placeholder="e.g. NSW" />
					</div>
					<div>
						<label for="dirInput">Direction from Previous City</label>
						<select id="dirInput">
							<option value="">Select direction</option>
							<option>N</option><option>NE</option><option>E</option><option>SE</option>
							<option>S</option><option>SW</option><option>W</option><option>NW</option>
						</select>
					</div>
				</div>

				<div class="row inline">
					<div><button id="submitBtn">Submit Answer</button></div>
					<div><button id="nextBtn" class="hidden">Next Question</button></div>
				</div>

				<div id="feedback"></div>

				<div id="mapArea">
					<p id="mapCaption"></p>
					<div id="map"></div>
				</div>
			</section>

			<section id="done" class="panel hidden">
				<h2>Quiz Complete</h2>
				<p id="finalScore"></p>
				<button id="restartBtn">Play Again</button>
			</section>
		</main>

		<script>
			const STATE_ALIASES = {
				"act": "Australian Capital Territory",
				"australian capital territory": "Australian Capital Territory",
				"nsw": "New South Wales",
				"new south wales": "New South Wales",
				"nt": "Northern Territory",
				"northern territory": "Northern Territory",
				"qld": "Queensland",
				"queensland": "Queensland",
				"sa": "South Australia",
				"south australia": "South Australia",
				"tas": "Tasmania",
				"tasmania": "Tasmania",
				"vic": "Victoria",
				"victoria": "Victoria",
				"wa": "Western Australia",
				"western australia": "Western Australia",
			};

			const DIR_ALIASES = {
				"n": "N", "north": "N",
				"ne": "NE", "northeast": "NE", "north-east": "NE",
				"e": "E", "east": "E",
				"se": "SE", "southeast": "SE", "south-east": "SE",
				"s": "S", "south": "S",
				"sw": "SW", "southwest": "SW", "south-west": "SW",
				"w": "W", "west": "W",
				"nw": "NW", "northwest": "NW", "north-west": "NW",
			};

			const setup = document.getElementById("setup");
			const quiz = document.getElementById("quiz");
			const done = document.getElementById("done");
			const startBtn = document.getElementById("startBtn");
			const restartBtn = document.getElementById("restartBtn");
			const submitBtn = document.getElementById("submitBtn");
			const nextBtn = document.getElementById("nextBtn");

			const cityNameEl = document.getElementById("cityName");
			const previousCityEl = document.getElementById("previousCity");
			const progressEl = document.getElementById("progress");
			const scoreEl = document.getElementById("score");
			const feedbackEl = document.getElementById("feedback");
			const finalScoreEl = document.getElementById("finalScore");
			const mapAreaEl = document.getElementById("mapArea");
			const mapCaptionEl = document.getElementById("mapCaption");

			const questionCountInput = document.getElementById("questionCount");
			const stateInput = document.getElementById("stateInput");
			const dirInput = document.getElementById("dirInput");

			let allCities = [];
			let order = [];
			let index = 1;
			let totalQuestions = 0;
			let totalChecks = 0;
			let correctChecks = 0;

			function normalizeText(s) {
				return (s || "").trim().toLowerCase().replace(/\\s+/g, " ");
			}

			function normalizeState(s) {
				const key = normalizeText(s);
				return STATE_ALIASES[key] || s.trim();
			}

			function normalizeDirection(s) {
				const key = normalizeText(s).replace(/\\s+/g, "");
				return DIR_ALIASES[key] || s.trim().toUpperCase();
			}

			function toRad(deg) {
				return (deg * Math.PI) / 180;
			}

			function bearingDegrees(lat1, lon1, lat2, lon2) {
				const phi1 = toRad(lat1);
				const phi2 = toRad(lat2);
				const dlambda = toRad(lon2 - lon1);
				const x = Math.sin(dlambda) * Math.cos(phi2);
				const y = Math.cos(phi1) * Math.sin(phi2) - Math.sin(phi1) * Math.cos(phi2) * Math.cos(dlambda);
				const theta = Math.atan2(x, y);
				return (theta * 180 / Math.PI + 360) % 360;
			}

			function bearingToCompass8(bearing) {
				const dirs = ["N", "NE", "E", "SE", "S", "SW", "W", "NW"];
				return dirs[Math.floor((bearing + 22.5) / 45) % 8];
			}

			function expectedDirection(prevCity, city) {
				const b = bearingDegrees(prevCity.latitude, prevCity.longitude, city.latitude, city.longitude);
				return bearingToCompass8(b);
			}

			function shuffle(array) {
				const arr = [...array];
				for (let i = arr.length - 1; i > 0; i--) {
					const j = Math.floor(Math.random() * (i + 1));
					[arr[i], arr[j]] = [arr[j], arr[i]];
				}
				return arr;
			}

			function setFeedback(stateOk, dirOk, expectedState, expectedDir) {
				const stateMessage = stateOk
					? "State: correct"
					: `State: wrong (correct: ${expectedState})`;
				const dirMessage = dirOk
					? "Direction: correct"
					: `Direction: wrong (correct: ${expectedDir})`;

				feedbackEl.innerHTML =
					`<div class="feedback-line ${stateOk ? "ok" : "bad"}">${stateMessage}</div>` +
					`<div class="feedback-line ${dirOk ? "ok" : "bad"}">${dirMessage}</div>`;
				feedbackEl.className = "show";
			}

			function clearInputs() {
				stateInput.value = "";
				dirInput.value = "";
				stateInput.focus();
			}

			function updateMeta() {
				progressEl.textContent = `Question ${index} / ${totalQuestions}`;
				scoreEl.textContent = `Score ${correctChecks}/${totalChecks}`;
			}

			function clamp(value, min, max) {
				return Math.min(max, Math.max(min, value));
			}

			function projectAustralia(lat, lon) {
				const minLon = 112;
				const maxLon = 154;
				const minLat = -44;
				const maxLat = -10;
				const x = (lon - minLon) / (maxLon - minLon);
				const y = (maxLat - lat) / (maxLat - minLat);
				return {
					x: clamp(x, 0, 1),
					y: clamp(y, 0, 1),
				};
			}

			function projectToCanvas(lat, lon, canvasW, canvasH) {
				const mapAspect = 765 / 577;
				const containerAspect = canvasW / canvasH;
				let imgW;
				let imgH;
				let offsetX;
				let offsetY;

				if (containerAspect > mapAspect) {
					imgH = canvasH;
					imgW = imgH * mapAspect;
					offsetX = (canvasW - imgW) / 2;
					offsetY = 0;
				} else {
					imgW = canvasW;
					imgH = imgW / mapAspect;
					offsetX = 0;
					offsetY = (canvasH - imgH) / 2;
				}

				// Calibrated to the visible Australia area inside the map image.
				const geoBox = {
					x0: 0.105,
					x1: 0.798,
					y0: 0.055,
					y1: 0.93,
				};

				const p = projectAustralia(lat, lon);
				const x = offsetX + (geoBox.x0 + p.x * (geoBox.x1 - geoBox.x0)) * imgW;
				const y = offsetY + (geoBox.y0 + p.y * (geoBox.y1 - geoBox.y0)) * imgH;
				return {
					x: clamp(x, 2, canvasW - 2),
					y: clamp(y, 2, canvasH - 2),
				};
			}

			function escapeHtml(text) {
				return String(text)
					.replace(/&/g, "&amp;")
					.replace(/</g, "&lt;")
					.replace(/>/g, "&gt;")
					.replace(/\"/g, "&quot;")
					.replace(/'/g, "&#39;");
			}

			function markerHtml(city, kind, canvasW, canvasH) {
				const p = projectToCanvas(city.latitude, city.longitude, canvasW, canvasH);
				const safeName = escapeHtml(city.name);
				return (
					`<div class="city-dot ${kind}" style="left:${p.x}px; top:${p.y}px;"></div>` +
					`<div class="city-label" style="left:${p.x}px; top:${p.y}px;">${safeName}</div>`
				);
			}

			function buildStaticAustraliaMapDataUri() {
				return "/assets/australia_states_map.jpg";
			}

			function showCityMap(prevCity, city) {
				const mapEl = document.getElementById("map");
				const mapImageSrc = buildStaticAustraliaMapDataUri();
				mapEl.innerHTML =
					`<div class="map-note">Australia states map (non-interactive)</div>` +
					`<div class="map-canvas">` +
					`<img class="map-image" src="${mapImageSrc}" alt="Australia states and territories map" />` +
					`<div class="marker-layer"></div>` +
					`</div>`;
				mapCaptionEl.textContent = `Map: ${prevCity.name} (previous) and ${city.name} (current)`;
				mapAreaEl.style.display = "block";

				const canvas = mapEl.querySelector(".map-canvas");
				const markerLayer = mapEl.querySelector(".marker-layer");
				const canvasW = canvas.clientWidth || 1;
				const canvasH = canvas.clientHeight || 1;
				markerLayer.innerHTML =
					markerHtml(prevCity, "previous", canvasW, canvasH) +
					markerHtml(city, "current", canvasW, canvasH);
			}

			function hideResultArea() {
				feedbackEl.className = "";
				feedbackEl.innerHTML = "";
				mapAreaEl.style.display = "none";
				nextBtn.classList.add("hidden");
				submitBtn.disabled = false;
			}

			function renderQuestion() {
				const city = order[index];
				const prev = order[index - 1];
				cityNameEl.textContent = city.name;
				previousCityEl.textContent = `Previous city: ${prev.name}`;
				updateMeta();
				hideResultArea();
				clearInputs();
			}

			function finishQuiz() {
				quiz.classList.add("hidden");
				done.classList.remove("hidden");
				const pct = totalChecks ? ((correctChecks / totalChecks) * 100).toFixed(1) : "0.0";
				finalScoreEl.textContent = `Final score: ${correctChecks}/${totalChecks} (${pct}%)`;
			}

			async function loadCities() {
				const res = await fetch("/api/cities");
				if (!res.ok) {
					throw new Error("Failed to load city data from server");
				}
				const payload = await res.json();
				return payload.cities;
			}

			async function startQuiz() {
				try {
					if (!allCities.length) {
						allCities = await loadCities();
					}
				} catch (err) {
					alert("Could not load city data. Check terminal for errors and restart server.");
					return;
				}

				const wanted = Number(questionCountInput.value || 20);
				const maxQ = Math.max(1, allCities.length - 1);
				totalQuestions = Math.max(1, Math.min(wanted, maxQ));

				order = shuffle(allCities).slice(0, totalQuestions + 1);
				index = 1;
				totalChecks = 0;
				correctChecks = 0;

				setup.classList.add("hidden");
				done.classList.add("hidden");
				quiz.classList.remove("hidden");
				renderQuestion();
			}

			function submitAnswer() {
				const city = order[index];
				const prev = order[index - 1];
				const expectedState = city.state;
				const expectedDir = expectedDirection(prev, city);

				const userState = normalizeState(stateInput.value);
				const userDir = normalizeDirection(dirInput.value);

				const stateOk = normalizeText(userState) === normalizeText(expectedState);
				const dirOk = userDir === expectedDir;

				totalChecks += 2;
				correctChecks += Number(stateOk) + Number(dirOk);

				setFeedback(stateOk, dirOk, expectedState, expectedDir);

				showCityMap(prev, city);
				submitBtn.disabled = true;
				nextBtn.classList.remove("hidden");
				nextBtn.textContent = index >= totalQuestions ? "Finish Quiz" : "Next Question";
				updateMeta();
			}

			function nextStep() {
				if (index >= totalQuestions) {
					finishQuiz();
					return;
				}
				index += 1;
				renderQuestion();
			}

			startBtn.addEventListener("click", startQuiz);
			restartBtn.addEventListener("click", () => {
				setup.classList.remove("hidden");
				done.classList.add("hidden");
				quiz.classList.add("hidden");
			});
			submitBtn.addEventListener("click", submitAnswer);
			nextBtn.addEventListener("click", nextStep);
			stateInput.addEventListener("keydown", (event) => {
				if (event.key === "Enter" && !submitBtn.disabled) {
					submitAnswer();
				}
			});
		</script>
	</body>
	</html>
	"""


@dataclass(frozen=True)
class CityRecord:
	name: str
	state: str
	population: int
	latitude: float
	longitude: float


def _normalize(s: str) -> str:
	return " ".join(s.strip().lower().split())


def normalize_state(user_input: str) -> str:
	key = _normalize(user_input)
	return STATE_ALIASES.get(key, user_input.strip())


def normalize_direction(user_input: str) -> str:
	key = _normalize(user_input).replace(" ", "")
	return DIRECTION_ALIASES.get(key, user_input.strip().upper())


def bearing_degrees(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
	"""Initial bearing in degrees from point 1 to point 2."""
	phi1 = math.radians(lat1)
	phi2 = math.radians(lat2)
	dlambda = math.radians(lon2 - lon1)

	x = math.sin(dlambda) * math.cos(phi2)
	y = math.cos(phi1) * math.sin(phi2) - math.sin(phi1) * math.cos(phi2) * math.cos(dlambda)
	theta = math.atan2(x, y)
	return (math.degrees(theta) + 360.0) % 360.0


def bearing_to_compass_8(bearing: float) -> str:
	directions = ["N", "NE", "E", "SE", "S", "SW", "W", "NW"]
	index = int((bearing + 22.5) // 45) % 8
	return directions[index]


def relative_direction(prev_city: CityRecord, current_city: CityRecord) -> str:
	b = bearing_degrees(prev_city.latitude, prev_city.longitude, current_city.latitude, current_city.longitude)
	return bearing_to_compass_8(b)


def _download_geonames_au_txt(cache_path: Path) -> None:
	cache_path.parent.mkdir(parents=True, exist_ok=True)
	try:
		with urllib.request.urlopen(GEONAMES_AU_ZIP_URL, timeout=30) as response:
			raw_zip = response.read()
	except urllib.error.URLError as exc:
		raise RuntimeError(
			"Could not download GeoNames data. Check internet connection and try again."
		) from exc

	with zipfile.ZipFile(io.BytesIO(raw_zip)) as zf:
		if GEONAMES_TXT_NAME not in zf.namelist():
			raise RuntimeError("GeoNames AU.zip did not contain AU.txt")
		with zf.open(GEONAMES_TXT_NAME) as src, cache_path.open("wb") as dst:
			dst.write(src.read())


def _download_map_image(cache_path: Path) -> None:
	cache_path.parent.mkdir(parents=True, exist_ok=True)
	req = urllib.request.Request(
		AU_STATES_MAP_URL,
		headers={"User-Agent": "Mozilla/5.0"},
	)
	try:
		with urllib.request.urlopen(req, timeout=30) as response:
			raw = response.read()
	except urllib.error.URLError as exc:
		raise RuntimeError("Could not download Australia states map image.") from exc

	if not raw:
		raise RuntimeError("Downloaded Australia states map image is empty.")

	cache_path.write_bytes(raw)


def ensure_map_image() -> Path:
	script_dir = Path(__file__).resolve().parent
	cache_path = script_dir / "data" / AU_STATES_MAP_NAME
	if not cache_path.exists():
		print("Downloading Australia states map image...")
		_download_map_image(cache_path)
	return cache_path


def haversine_km(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
	radius_km = 6371.0
	dlat = math.radians(lat2 - lat1)
	dlon = math.radians(lon2 - lon1)
	a = (
		math.sin(dlat / 2) ** 2
		+ math.cos(math.radians(lat1))
		* math.cos(math.radians(lat2))
		* math.sin(dlon / 2) ** 2
	)
	c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
	return radius_km * c


def _select_independent_cities_per_territory(
	rows: list[CityRecord],
	per_territory: int,
) -> tuple[list[CityRecord], dict[str, int]]:
	states = list(ADMIN1_TO_STATE.values())
	grouped: dict[str, list[CityRecord]] = {state: [] for state in states}
	for city in rows:
		grouped.setdefault(city.state, []).append(city)

	for state in states:
		grouped[state].sort(key=lambda c: c.population, reverse=True)

	selected_all: list[CityRecord] = []
	shortages: dict[str, int] = {}

	for state in states:
		candidates = grouped[state]
		picked: list[CityRecord] = []

		for min_sep_km in SEPARATION_STEPS_KM:
			for city in candidates:
				if city in picked:
					continue
				if len(picked) >= per_territory:
					break

				too_close = any(
					haversine_km(city.latitude, city.longitude, chosen.latitude, chosen.longitude) < min_sep_km
					for chosen in picked
				)
				if not too_close:
					picked.append(city)

			if len(picked) >= per_territory:
				break

		if len(picked) < per_territory:
			shortages[state] = per_territory - len(picked)

		selected_all.extend(picked)

	return selected_all, shortages


def load_quiz_cities_from_geonames(per_territory: int = CITIES_PER_TERRITORY) -> tuple[list[CityRecord], dict[str, int]]:
	script_dir = Path(__file__).resolve().parent
	cache_path = script_dir / "data" / GEONAMES_TXT_NAME

	if not cache_path.exists():
		print("Downloading latest Australia city data from GeoNames...")
		_download_geonames_au_txt(cache_path)

	rows: list[CityRecord] = []
	seen: set[tuple[str, str]] = set()

	with cache_path.open("r", encoding="utf-8", newline="") as f:
		reader = csv.reader(f, delimiter="\t")
		for cols in reader:
			if len(cols) < 19:
				continue

			feature_class = cols[6]
			feature_code = cols[7]
			if feature_class != "P":
				continue
			if feature_code not in INDEPENDENT_FEATURE_CODES:
				continue

			name = cols[1].strip()
			admin1_code = cols[10].strip()
			state = ADMIN1_TO_STATE.get(admin1_code)
			if not name or not state:
				continue

			try:
				latitude = float(cols[4])
				longitude = float(cols[5])
				population = int(cols[14] or 0)
			except ValueError:
				continue

			if population <= 0:
				continue

			dedupe_key = (_normalize(name), state)
			if dedupe_key in seen:
				continue

			seen.add(dedupe_key)
			rows.append(
				CityRecord(
					name=name,
					state=state,
					population=population,
					latitude=latitude,
					longitude=longitude,
				)
			)

	rows.sort(key=lambda c: c.population, reverse=True)
	return _select_independent_cities_per_territory(rows, per_territory)


class QuizHandler(BaseHTTPRequestHandler):
	cities_payload: list[dict[str, object]] = []
	map_image_path: Path | None = None

	def _send_json(self, payload: dict[str, object], status: int = 200) -> None:
		raw = json.dumps(payload).encode("utf-8")
		self.send_response(status)
		self.send_header("Content-Type", "application/json; charset=utf-8")
		self.send_header("Content-Length", str(len(raw)))
		self.end_headers()
		self.wfile.write(raw)

	def _send_html(self, html: str, status: int = 200) -> None:
		raw = html.encode("utf-8")
		self.send_response(status)
		self.send_header("Content-Type", "text/html; charset=utf-8")
		self.send_header("Content-Length", str(len(raw)))
		self.end_headers()
		self.wfile.write(raw)

	def _send_binary(self, raw: bytes, content_type: str, status: int = 200) -> None:
		self.send_response(status)
		self.send_header("Content-Type", content_type)
		self.send_header("Content-Length", str(len(raw)))
		self.end_headers()
		self.wfile.write(raw)

	def do_GET(self) -> None:
		parsed = urlparse(self.path)
		if parsed.path in ("/", "/index.html"):
			self._send_html(HTML_PAGE)
			return

		if parsed.path == "/api/cities":
			self._send_json({"cities": self.cities_payload})
			return

		if parsed.path == "/assets/australia_states_map.jpg":
			if self.map_image_path and self.map_image_path.exists():
				self._send_binary(self.map_image_path.read_bytes(), "image/jpeg")
				return
			self._send_json({"error": "Map image missing"}, status=404)
			return

		self._send_json({"error": "Not found"}, status=404)


def build_cities_payload(cities: list[CityRecord]) -> list[dict[str, object]]:
	return [
		{
			"name": c.name,
			"state": c.state,
			"population": c.population,
			"latitude": c.latitude,
			"longitude": c.longitude,
		}
		for c in cities
	]


def run_web_server(cities: list[CityRecord], map_image_path: Path, host: str = "127.0.0.1", port: int = 8000) -> None:
	QuizHandler.cities_payload = build_cities_payload(cities)
	QuizHandler.map_image_path = map_image_path
	server = ThreadingHTTPServer((host, port), QuizHandler)
	print(f"Server running on http://{host}:{port}")
	print("Open that URL in your browser. Press Ctrl+C to stop.")
	server.serve_forever()


def print_intro() -> None:
	msg = """
	This app serves a local website quiz using the GeoNames Australia dataset.
	It keeps up to 15 independent cities per state/territory and randomizes
	city order on each new quiz run in the browser.

	First run downloads data and caches it in ./data/AU.txt.
	"""
	print(textwrap.dedent(msg).strip())


def main() -> int:
	print_intro()
	try:
		cities, shortages = load_quiz_cities_from_geonames(per_territory=CITIES_PER_TERRITORY)
	except Exception as exc:
		print(f"Error loading city data: {exc}")
		return 1

	expected = len(ADMIN1_TO_STATE) * CITIES_PER_TERRITORY
	if len(cities) < expected:
		print(f"Warning: only loaded {len(cities)}/{expected} selected cities.")
		for state, missing in shortages.items():
			print(f"  {state}: missing {missing}")

	try:
		map_image_path = ensure_map_image()
	except Exception as exc:
		print(f"Error loading map image: {exc}")
		return 1

	try:
		run_web_server(cities, map_image_path=map_image_path)
	except KeyboardInterrupt:
		print("\nServer stopped.")
	return 0


if __name__ == "__main__":
	sys.exit(main())
