# 현대기하학과 응용 학습지 작업 규칙

## 작업 방식
- 원본: 현대기하학과 응용.pdf
- 각 절마다 원본 페이지를 직접 이미지로 확인(pdftoppm 또는 view)한 뒤 내용 재구성
- OCR 텍스트가 있다면 참고만 하고, 이미지로 직접 검증할 것
- 수식/도형 설명이 깨진 경우 앞뒤 맥락(정의, 정리, 예제 풀이)으로 역산해서 정합성 확인

## LaTeX 스타일 (이전 프로젝트들과 동일)
- 정의/핵심규칙 박스: tcolorbox, colback=teal!4, colframe=teal!65!black
  - 박스 안에서 "정의"와 "핵심 규칙"을 \rule로 구분
- 정리(theorem) 박스: colback=red!4, colframe=red!60!black
- 장 시작 개요 박스: colback=blue!5, colframe=blue!60!black
- 모든 표는 세로줄 포함 (|l|l|l| 형식)
- 예제는 \subsection*{EXAMPLE n} 형식, SOLUTION은 \textbf{SOLUTION:}

## 이미지
- 순수 TikZ 또는 pgfplots로 벡터 그림 생성, 원본 스캔 이미지는 쓰지 않음
- 매 그림마다 xelatex로 컴파일 테스트, standalone 클래스로 크롭해서 가로세로 비율 확인 후 코드 제출

### 장별 도형 유형 및 도구

**제 1 장 (유클리드 기하학)** — 순수 TikZ 2D
- 반사: 거울선(dashed), 점과 상점을 잇는 수선, 수직 이등분 표시
- 평행 이동·회전: 화살표(->), 호(arc), 각도 표시(\markangle 또는 pic{angle})
- 합동 삼각형: 대응 꼭짓점에 눈금(tick) 표시, 각도 호 중복 표시
- 좌표계 필요 시 \draw[->] 축만 그림, 격자 없음

**제 2 장 (구면 기하학)** — pgfplots 3D + TikZ 2D 혼용
- 구면·대원·구면 삼각형: pgfplots `\addplot3[surf]` 또는 TikZ `\draw (0,0) circle (r)` + 타원(대원 투영)
- 측지선(대원호): `\tdplotsetmaincoords`(tdplot 패키지) 또는 pgfplots `parametric` 곡선
- 입체 사영(stereographic projection): TikZ 2D, 구의 단면원 + 투영선 + 평면
- 지도(2.9): TikZ 2D 메르카토르/방위 도법 격자, 항로선(loxodrome)은 곡선으로 근사

**제 4 장 (사영 기하학)** — 순수 TikZ 2D
- 원근법·소실점: 수렴하는 직선 다발, 소실점에 \node
- 데자르그 정리·파스칼·브리앙송: 삼각형 + 연장선 교점, 색상으로 대응 요소 구분
- 복비: 직선 위 네 점, 비율 레이블
- 원뿔곡선(타원·쌍곡선·포물선): `\draw plot[domain=...]` 또는 pgfplots 2D
- 쌍대 곡선·접선: 원뿔곡선 + 접선 묶음(envelope 느낌)

## 산출물
- 모든 .tex 파일은 작성 후 반드시 xelatex로 컴파일해서 같은 폴더에 .pdf까지 생성
- 컴파일 에러가 나면 로그를 스스로 읽고 고친 뒤 재컴파일