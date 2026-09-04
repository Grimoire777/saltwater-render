FROM node:20-alpine

RUN apk add --no-cache ffmpeg

WORKDIR /app

COPY package.json ./
RUN npm install --omit=dev

COPY server.js ./

ENV DATA_DIR=/data
ENV PORT=8080
EXPOSE 8080

CMD ["node", "server.js"]
