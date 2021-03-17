# ffmpeg

# convert to mp4

	find . -iname 'IMG*.mov' |xargs -I {} ffmpeg -i {} -vcodec copy -acodec copy $(basename {} ".mov").mp4


# split video into multiple parts

	ffmpeg -i IMG_1802.mp4  -vcodec copy -acodec copy -map 0 -segment_time 14 -f segment output_video%02d.mp4

.
