// --- DOM 元素引用 ---
const videoElement = document.getElementsByClassName('input_video')[0];
const canvasElement = document.getElementsByClassName('output_canvas')[0];
const canvasCtx = canvasElement.getContext('2d');
const statusDiv = document.getElementById('status');
const debugDiv = document.getElementById('debug-info');
const alarmSound = document.getElementById('alarm-sound'); 
const toggleCameraBtn = document.getElementById('toggleCamera');
const toggleDisplayBtn = document.getElementById('toggleDisplay');
const toggleChartBtn = document.getElementById('toggleChart');
const chartContainer = document.getElementById('chartContainer');
const ctx = document.getElementById('perclosChart').getContext('2d');
const metricTime = document.getElementById('metric-time');
const metricAlarms = document.getElementById('metric-alarms');
const metricBPM = document.getElementById('metric-bpm');
const metricPERCLOS = document.getElementById('metric-perclos');
// V8.0 新增指標引用
const metricPitch = document.getElementById('metric-pitch');
const metricYaw = document.getElementById('metric-yaw');

const loaderDiv = document.getElementById('loader');
const loadProgressDiv = document.getElementById('load-progress');
const volumeSlider = document.getElementById('volumeSlider'); 
const volumeValueSpan = document.getElementById('volumeValue'); 
const unlockAudioBtn = document.getElementById('unlockAudioBtn');

// --- 核心參數設定 ---
const EAR_THRESHOLD = 0.25; 
const LONG_CLOSE_TIME = 1.5; 
const PERCLOS_THRESHOLD = 0.25; 
const PERCLOS_WINDOW_SIZE = 600; 
// V8.0 新增：分心偵測角度閾值 (度)
const HEAD_PITCH_THRESHOLD = 15; // 低頭超過 15度
const HEAD_YAW_THRESHOLD = 20;   // 轉頭超過 20度

const CALIBRATION_TIME = 5; 
const ASSUMED_FPS = 30; 
const CALIBRATION_FRAMES = CALIBRATION_TIME * ASSUMED_FPS; 
const BPM_WINDOW = 300; 
const CHART_RECORD_INTERVAL = 5 * ASSUMED_FPS; 
const MAX_LOW_FPS_TIME = 3; 
const LOW_FPS_THRESHOLD = 5; 
const INIT_TIMEOUT = 10000; 

let frameCount = 0;
let closedFrameCount = 0;
let closedFrameHistory = [];
let calibrationComplete = false;
let calibrationFramesLeft = CALIBRATION_FRAMES;
let totalAlarmCount = 0;
let blinkHistory = [];
let isDangerState = false; 
let isCameraActive = false;
let isDisplayActive = true; 
let isChartRealtime = false; 
let camera = null;
let faceMesh = null;
let startTime = Date.now() / 1000;
let chartData = []; 
let perclosChart = null; 
let lastFrameTime = Date.now();
let lowFpsDuration = 0;
let initTimer = null; 
let initStartTime = 0;

function resizeCanvas() {
    canvasElement.width = window.innerWidth;
    canvasElement.height = window.innerHeight * 0.5; 
}
window.addEventListener('resize', resizeCanvas);
resizeCanvas();

function euclideanDistance(p1, p2) {
    return Math.sqrt(Math.pow(p1.x - p2.x, 2) + Math.pow(p1.y - p2.y, 2));
}

function calculateEAR(landmarks, indices) {
    const p1 = landmarks[indices[0]];
    const p4 = landmarks[indices[3]];
    const p2 = landmarks[indices[1]];
    const p6 = landmarks[indices[5]];
    const p3 = landmarks[indices[2]];
    const p5 = landmarks[indices[4]];
    
    const vertical1 = euclideanDistance(p2, p6);
    const vertical2 = euclideanDistance(p3, p5);
    const horizontal = euclideanDistance(p1, p4);
    return (vertical1 + vertical2) / (2.0 * horizontal);
}

// --- V8.0 新增：頭部姿態計算 (Pitch 和 Yaw) ---
function calculateHeadPose(landmarks) {
    // 選擇關鍵點用於姿勢估計 (基於 FaceMesh 索引)
    const Nose = landmarks[1];
    const Chin = landmarks[152];
    const LeftEyeCorner = landmarks[226]; // 接近左眼內角
    const RightEyeCorner = landmarks[446]; // 接近右眼內角
    const LeftMouthCorner = landmarks[61];
    const RightMouthCorner = landmarks[291];

    // 將地標從正規化座標 (0-1) 轉換為畫布像素座標
    const W = canvasElement.width;
    const H = canvasElement.height;
    const toPixel = (p) => ({ 
        x: p.x * W, 
        y: p.y * H, 
        z: p.z * W 
    });

    const points = [Nose, Chin, LeftEyeCorner, RightEyeCorner, LeftMouthCorner, RightMouthCorner].map(toPixel);

    // Pitch 近似 (低頭為正，抬頭為負)
    const nose_chin_y_dist = points[1].y - points[0].y;
    const eye_dist_y = points[2].y - points[3].y;
    const reference_pitch_dist = Math.abs(points[2].x - points[3].x) * 1.5; 
    
    let pitch = 0;
    if (reference_pitch_dist > 0) {
         // 角度 = atan2(對邊, 鄰邊) * (180/PI)
         pitch = Math.atan2(points[0].y - points[1].y, points[0].z - points[1].z) * (180 / Math.PI) * -1;
    }

    // Yaw 近似 (左轉為正，右轉為負)
    const left_right_eye_x_mid = (points[2].x + points[3].x) / 2;
    const mouth_x_mid = (points[4].x + points[5].x) / 2;
    const yaw_mid_diff = mouth_x_mid - left_right_eye_x_mid;

    const face_width = euclideanDistance(points[2], points[3]);
    let yaw = 0;
    if (face_width > 0) {
         yaw = Math.atan2(yaw_mid_diff, face_width) * (180 / Math.PI) * 2;
    }
    
    pitch = pitch * 1.2;
    yaw = yaw * 1.5;
    
    return { pitch: pitch, yaw: yaw };
}


function getDrawColor(status) {
    switch (status) {
        case 'safe': return '#27ae60'; 
        case 'warning': return '#f39c12'; 
        case 'danger': return '#e74c3c'; 
        default: return '#f39c12';
    }
}

function drawEyeBoundingBox(landmarks, indices, color) {
    if (!isDisplayActive || !landmarks || landmarks.length === 0) return;
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const index of indices) {
        const p = landmarks[index];
        const x = p.x * canvasElement.width;
        const y = p.y * canvasElement.height;
        minX = Math.min(minX, x);
        minY = Math.min(minY, y);
        maxX = Math.max(maxX, x);
        maxY = Math.max(maxY, y);
    }
    const padding = 10; 
    minX -= padding; minY -= padding; maxX += padding; maxY += padding;
    const width = maxX - minX;
    const height = maxY - minY;
    canvasCtx.beginPath();
    canvasCtx.strokeStyle = color; 
    canvasCtx.lineWidth = 4; 
    canvasCtx.rect(minX, minY, width, height);
    canvasCtx.stroke();
}

function formatTime(seconds) {
    const h = String(Math.floor(seconds / 3600)).padStart(2, '0');
    const m = String(Math.floor((seconds % 3600) / 60)).padStart(2, '0');
    const s = String(Math.floor(seconds % 60)).padStart(2, '0');
    return `${h}:${m}:${s}`;
}

function initChart() {
     if (perclosChart) { perclosChart.destroy(); }
     perclosChart = new Chart(ctx, { 
        type: 'line',
        data: {
            labels: chartData.map(d => d.x),
            datasets: [{
                label: 'PERCLOS (%)',
                data: chartData.map(d => d.y),
                borderColor: '#3498db',
                backgroundColor: 'rgba(52, 152, 219, 0.2)',
                fill: true, tension: 0.1, pointRadius: 2
            },
            {
                label: `疲勞閾值 (${PERCLOS_THRESHOLD*100}%)`,
                data: chartData.map(d => PERCLOS_THRESHOLD * 100),
                borderColor: '#e74c3c',
                borderWidth: 2, borderDash: [5, 5], pointRadius: 0, fill: false
            }]
        },
        options: {
            animation: { duration: 500 }, 
            responsive: true, maintainAspectRatio: false,
            scales: {
                x: { title: { display: true, text: '時間 (秒)' } },
                y: { title: { display: true, text: 'PERCLOS (%)' }, min: 0, max: 100, }
            },
            plugins: { legend: { display: true } }
        }
    });
    chartContainer.style.display = 'block';
}

function updateChart(mode = 'none') {
    if (!perclosChart) return;
    perclosChart.data.labels = chartData.map(d => d.x);
    perclosChart.data.datasets[0].data = chartData.map(d => d.y);
    perclosChart.data.datasets[1].data = chartData.map(d => PERCLOS_THRESHOLD * 100); 
    perclosChart.update(mode); 
}

function processFatigue(avgEAR, headPose) { 
    if (!isCameraActive || !calibrationComplete) return 'warning';

    // --- FPS/卡頓檢查 ---
    const currentTime = Date.now();
    const fps = 1000 / (currentTime - lastFrameTime);
    lastFrameTime = currentTime;

    if (fps < LOW_FPS_THRESHOLD) {
        lowFpsDuration += (currentTime - lastFrameTime) / 1000;
    } else {
        lowFpsDuration = 0;
    }
    
    if (lowFpsDuration >= MAX_LOW_FPS_TIME) {
         statusDiv.innerText = `🚨 嚴重卡頓！系統將在 3 秒後自動關閉相機保護系統。`;
         statusDiv.className = 'status-text danger';
         if (navigator.vibrate) navigator.vibrate([100, 100, 100]); 
         
         setTimeout(() => {
             if (isCameraActive) {
                 alert("系統檢測到嚴重卡頓，已自動關閉相機以保護裝置穩定。");
                 stopCamera();
             }
         }, 3000); 
         lowFpsDuration = -Infinity; 
         return 'danger';
    }


    // --- 疲勞偵測邏輯 ---
    const isClosed = avgEAR < EAR_THRESHOLD;
    closedFrameHistory.push(isClosed ? 1 : 0);
    if (closedFrameHistory.length > PERCLOS_WINDOW_SIZE) {
        closedFrameHistory.shift(); 
    }

    const closedFramesInWindow = closedFrameHistory.reduce((sum, val) => sum + val, 0);
    const currentPERCLOS = closedFramesInWindow / closedFrameHistory.length;
    
    let alarmTriggered = false;
    let newStatusColor = 'safe';
    let statusMessage = "✅ 駕駛清醒";


    // --- V8.0 分心偵測邏輯 ---
    const { pitch, yaw } = headPose;
    const isLookingDown = pitch > HEAD_PITCH_THRESHOLD;  
    const isLookingAway = Math.abs(yaw) > HEAD_YAW_THRESHOLD; 

    // V8.0: 優先級：分心 > 疲勞 > 清醒
    if (isLookingDown) {
        statusMessage = `⚠️ 低頭分心！俯仰角 ${pitch.toFixed(1)}° (危險)`;
        newStatusColor = 'danger';
        alarmTriggered = true;
    } else if (isLookingAway) {
        statusMessage = `⚠️ 轉頭分心！偏航角 ${yaw.toFixed(1)}° (警告)`;
        newStatusColor = 'warning';
        alarmTriggered = true;
    }
    // 疲勞偵測 (只在未分心時檢查)
    else if (isClosed) {
        closedFrameCount++;
        const closedSeconds = closedFrameCount / (frameCount / (Date.now() / 1000 - startTime));

        if (closedSeconds >= LONG_CLOSE_TIME) {
            statusMessage = `🚨 危險！閉眼超過 ${closedSeconds.toFixed(1)} 秒 (睡著了!)`;
            newStatusColor = 'danger';
            alarmTriggered = true;
        }
    } else {
        if (closedFrameCount > 1) { 
            blinkHistory.push(frameCount); 
        }
        closedFrameCount = 0;
    }

    if (currentPERCLOS >= PERCLOS_THRESHOLD && !alarmTriggered) {
        statusMessage = `⚠️ 極度疲勞！PERCLOS 達 ${(currentPERCLOS * 100).toFixed(1)}%`;
        newStatusColor = 'danger';
        alarmTriggered = true;
    } 
    
    statusDiv.innerText = statusMessage;
    
    // --- V7.1 核心：音效播放與停止邏輯 ---
    if (alarmTriggered) {
        if (!isDangerState) {
            totalAlarmCount++;
            isDangerState = true;
            alarmSound.play().catch(e => console.log("音效播放失敗 (可能需要用戶互動):", e)); 
            if (navigator.vibrate) navigator.vibrate([200, 100, 200]); 
        }
    } else {
        if (isDangerState) {
            alarmSound.pause();
            alarmSound.currentTime = 0; 
        }
        isDangerState = false;
    }
    
    // --- 儀表板更新 ---
    const totalSeconds = Math.floor(Date.now() / 1000 - startTime);
    metricTime.innerText = formatTime(totalSeconds);
    metricAlarms.innerText = `${totalAlarmCount} 次`;
    metricPERCLOS.innerText = `${(currentPERCLOS * 100).toFixed(1)} %`;
    // V8.0: 更新新的儀表板指標
    metricPitch.innerText = `${pitch.toFixed(1)} °`;
    metricYaw.innerText = `${yaw.toFixed(1)} °`;
    
    const frameWindow = frameCount - BPM_WINDOW;
    blinkHistory = blinkHistory.filter(f => f > frameWindow);
    const timeElapsed = (frameCount - frameWindow) / fps;
    const currentBPM = timeElapsed > 0 ? (blinkHistory.length / timeElapsed) * 60 : 0;
    metricBPM.innerText = `${Math.round(currentBPM)} BPM`;
    
    if (frameCount > 0 && frameCount % CHART_RECORD_INTERVAL === 0) {
         const perclosPct = currentPERCLOS * 100;
         const timeLabel = totalSeconds;
         chartData.push({ x: timeLabel, y: perclosPct });
         if (isChartRealtime && perclosChart) { updateChart('none'); }
    }
    
    debugDiv.innerText = `閉眼時長: ${(closedFrameCount / (frameCount / (Date.now() / 1000 - startTime))).toFixed(2)} 秒 | 實時 FPS: ${fps.toFixed(1)}`;
    
    return newStatusColor;
}

function onResults(results) {
    clearTimeout(initTimer); 
    loaderDiv.style.display = 'none'; 

    canvasCtx.save();
    canvasCtx.clearRect(0, 0, canvasElement.width, canvasElement.height);
    
    if (isCameraActive && isDisplayActive && results.image) {
        canvasCtx.drawImage(results.image, 0, 0, canvasElement.width, canvasElement.height);
    }

    let statusForDrawing = 'warning'; 
    let avgEAR = 0;
    let headPose = { pitch: 0, yaw: 0 };

    if (isCameraActive && results.multiFaceLandmarks && results.multiFaceLandmarks.length > 0) {
        const landmarks = results.multiFaceLandmarks[0];
        const leftEyeIndices = [33, 160, 158, 133, 153, 144]; 
        const rightEyeIndices = [362, 385, 387, 263, 373, 380];
        avgEAR = (calculateEAR(landmarks, leftEyeIndices) + calculateEAR(landmarks, rightEyeIndices)) / 2;
        
        // V8.0: 計算頭部姿勢
        headPose = calculateHeadPose(landmarks);

        if (!calibrationComplete) {
            frameCount++; 
            calibrationFramesLeft--;
            statusForDrawing = 'warning'; 
            const timeLeft = Math.max(0, (calibrationFramesLeft / ASSUMED_FPS)).toFixed(1); 
            statusDiv.innerText = `⚙️ 系統校準中... 請自然眨眼，剩餘 ${timeLeft} 秒`;
            debugDiv.innerText = `校準中 (5秒)... 請保持臉部不動`;
            statusDiv.className = "status-text warning"; 
            
            if (calibrationFramesLeft <= 0) {
                calibrationComplete = true;
                startTime = Date.now() / 1000;
                frameCount = 0; 
                debugDiv.innerText = '✅ 校準完成！開始疲勞偵測。';
            }
        } else {
            frameCount++;
            let currentStatusColor = processFatigue(avgEAR, headPose); 
            statusForDrawing = currentStatusColor;
            statusDiv.className = `status-text ${currentStatusColor}`;
        }
        
        if (isDisplayActive) {
            drawEyeBoundingBox(landmarks, leftEyeIndices, getDrawColor(statusForDrawing));
            drawEyeBoundingBox(landmarks, rightEyeIndices, getDrawColor(statusForDrawing));
        }
        
    } else if (isCameraActive) {
         statusDiv.innerText = `🚨 請將臉部對準鏡頭！`;
         statusDiv.className = `status-text danger`;
         statusForDrawing = 'danger';
         metricBPM.innerText = `N/A`;
         metricPERCLOS.innerText = `N/A`;
         metricPitch.innerText = `N/A`; 
         metricYaw.innerText = `N/A`; 
    }
    canvasCtx.restore();
}

function initTimeoutHandler() {
    if (isCameraActive) return; 
    loaderDiv.style.display = 'none'; 
    statusDiv.className = 'status-text danger';
    
    if (navigator.mediaDevices && navigator.mediaDevices.getUserMedia) {
        statusDiv.innerText = `❌ 初始化超時 (10秒)。可能原因：相機權限或裝置被佔用。`;
        debugDiv.innerHTML = `
            **建議排錯步驟:**<br>
            1. **通訊軟體內嵌:** 嘗試使用 Chrome/Safari **標準瀏覽器**開啟，而非通訊軟體內的瀏覽器。<br>
            2. **相機權限:** 檢查瀏覽器網址列鎖頭圖標，確認相機權限已開啟。<br>
            3. **重啟裝置:** 確保相機沒有被其他 App (如 Zoom, Line) 佔用。
        `;
    } else {
         statusDiv.innerText = `❌ 錯誤：您的瀏覽器或裝置不支援相機功能。`;
         debugDiv.innerText = `請嘗試更新您的瀏覽器或在支援的裝置上使用。`;
    }
}

function stopCamera() {
    clearTimeout(initTimer);
    lowFpsDuration = 0; 
    
    alarmSound.pause();
    alarmSound.currentTime = 0;

    if (camera) {
        camera.stop();
        const tracks = videoElement.srcObject ? videoElement.srcObject.getTracks() : [];
        tracks.forEach(track => track.stop());
        videoElement.srcObject = null;
        isCameraActive = false;
        canvasCtx.clearRect(0, 0, canvasElement.width, canvasElement.height);
    }
    toggleCameraBtn.innerText = '開啟鏡頭';
    toggleCameraBtn.classList.add('off');
    statusDiv.innerText = '🎥 鏡頭已關閉，正在總結數據...';
    statusDiv.className = 'status-text warning';

    if (chartData.length > 0) {
         initChart();
         updateChart('normal'); 
         debugDiv.innerText = '總結圖表已生成。';
    } else {
         chartContainer.style.display = 'none';
         debugDiv.innerText = '鏡頭已關閉。無數據可供總結。';
    }
    isChartRealtime = false;
    toggleChartBtn.innerText = '顯示總結圖表';
    toggleChartBtn.classList.remove('realtime');
}

function startCamera() {
    initStartTime = Date.now();
    loaderDiv.style.display = 'flex';
    loadProgressDiv.innerText = '0%';
    
    initTimer = setTimeout(initTimeoutHandler, INIT_TIMEOUT);

    const updateLoader = setInterval(() => {
        const elapsed = Date.now() - initStartTime;
        const progress = Math.min(100, Math.floor((elapsed / INIT_TIMEOUT) * 100));
        loadProgressDiv.innerText = `${progress}%`;
        if (progress >= 100) clearInterval(updateLoader);
        if (isCameraActive) clearInterval(updateLoader);
    }, 100);

    if (camera) {
        chartContainer.style.display = 'none'; 
        camera.start().then(() => {
            isCameraActive = true;
            calibrationComplete = false;
            calibrationFramesLeft = CALIBRATION_FRAMES;
            frameCount = 0;
            toggleCameraBtn.innerText = '關閉鏡頭';
            toggleCameraBtn.classList.remove('off');
            clearTimeout(initTimer); 
            loaderDiv.style.display = 'none';
        }).catch(error => {
            clearTimeout(initTimer);
            loaderDiv.style.display = 'none';
            initTimeoutHandler(); 
            console.error("Camera Start Error:", error);
        });
    } else {
         statusDiv.innerText = '初始化失敗，請檢查權限';
         statusDiv.className = 'status-text danger';
         loaderDiv.style.display = 'none';
    }
}

function toggleDisplay() {
    isDisplayActive = !isDisplayActive;
    if (isDisplayActive) {
        canvasElement.classList.remove('hidden');
        toggleDisplayBtn.innerText = '關閉影像顯示';
        toggleDisplayBtn.classList.remove('off');
    } else {
        canvasElement.classList.add('hidden');
        toggleDisplayBtn.innerText = '開啟影像顯示';
        toggleDisplayBtn.classList.add('off');
        canvasCtx.clearRect(0, 0, canvasElement.width, canvasElement.height); 
    }
}

function toggleChartDisplay() {
    if (isCameraActive) {
        isChartRealtime = !isChartRealtime;
        if (isChartRealtime) {
            initChart(); 
            updateChart('normal'); 
            toggleChartBtn.innerText = '關閉實時圖表 (高 CPU)';
            toggleChartBtn.classList.add('realtime');
            debugDiv.innerText = '警告：已開啟實時圖表，可能增加 CPU 負載！';
        } else {
            chartContainer.style.display = 'none';
            toggleChartBtn.innerText = '開啟實時圖表';
            toggleChartBtn.classList.remove('realtime');
            debugDiv.innerText = '實時圖表已關閉，數據仍在後台紀錄。';
        }
    } else {
        if (chartContainer.style.display === 'block') {
            chartContainer.style.display = 'none';
            toggleChartBtn.innerText = '隱藏總結圖表';
        } else if (chartData.length > 0) {
            initChart();
            updateChart('normal');
            toggleChartBtn.innerText = '隱藏總結圖表';
        } else {
            debugDiv.innerText = '目前沒有疲勞數據可以總結。';
        }
    }
}

function initVolumeControl() {
    // 初始音量設定為滑桿值 (50/100 = 0.5)
    alarmSound.volume = volumeSlider.value / 100;
    volumeValueSpan.innerText = `${volumeSlider.value}%`;

    volumeSlider.addEventListener('input', (event) => {
        const volumePercent = event.target.value;
        alarmSound.volume = volumePercent / 100; 
        volumeValueSpan.innerText = `${volumePercent}%`;
    });
}

function unlockAudio() {
    // 1. V7.1.2：視覺提示 - 點擊後立即變綠 (表示正在嘗試解鎖)
    unlockAudioBtn.classList.add('success'); 
    unlockAudioBtn.innerText = '✅ 正在解鎖...';
    
    // 嘗試靜音播放，如果成功，表示瀏覽器已授予播放權限
    alarmSound.muted = true; 
    alarmSound.play()
        .then(() => {
            // 播放成功 (權限已授予)
            alarmSound.pause();
            alarmSound.currentTime = 0;
            alarmSound.muted = false; // 恢復正常音量控制
            
            // 2. V7.1.2：成功後隱藏按鈕
            unlockAudioBtn.style.display = 'none'; 
            debugDiv.innerText = '✅ 警報音效已成功解鎖並啟用。';
        })
        .catch(e => {
            // 播放失敗 (用戶需要更多互動)
            // 3. V7.1.2：失敗後恢復橙色，提示用戶需要更多互動
            unlockAudioBtn.classList.remove('success');
            unlockAudioBtn.innerText = '⚠️ 點擊解鎖失敗 (請嘗試調整音量滑桿)';
            debugDiv.innerText = '⚠️ 音效仍被鎖定。請嘗試調整音量滑桿或再次點擊按鈕。';
            alarmSound.muted = false;
        });
}


// --- 啟動與初始化 ---
function initializeApp() {
     faceMesh = new FaceMesh({locateFile: (file) => {
        return `https://cdn.jsdelivr.net/npm/@mediapipe/face_mesh/${file}`;
    }});
    
    faceMesh.setOptions({
        maxNumFaces: 1,
        refineLandmarks: true,
        minDetectionConfidence: 0.5,
        minTrackingConfidence: 0.5
    });
    faceMesh.onResults(onResults);

    camera = new Camera(videoElement, {
        onFrame: async () => {
            if (isCameraActive) {
                await faceMesh.send({image: videoElement});
            }
        },
        width: 1280, 
        height: 720,
        facingMode: "user"
    });
    
    // 綁定事件
    toggleCameraBtn.addEventListener('click', () => {
        if (isCameraActive) { stopCamera(); } else { startCamera(); }
    });
    toggleDisplayBtn.addEventListener('click', toggleDisplay);
    toggleChartBtn.addEventListener('click', toggleChartDisplay);
    
    // V7.1.1 綁定解鎖按鈕事件
    unlockAudioBtn.addEventListener('click', unlockAudio); 
    
    // 啟動音量控制
    initVolumeControl(); 

    // 系統啟動
    setTimeout(startCamera, 500);
    
    // V7.1.1 啟動時提示用戶互動
    debugDiv.innerText = '⚠️ 請先點擊「解鎖警報音效」按鈕或調整音量滑桿以啟用警報。';
    alarmSound.muted = false; 
}

initializeApp();
