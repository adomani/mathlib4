#!/usr/bin/env python3
import sys
import zulip
import re
import json

# Usage:
# python listenZulip.py $ZULIP_API_KEY $ZULIP_EMAIL $ZULIP_SITE $NUMBER_OF_COMMENTS_TO_SCAN
# The first three variables identify the lean4 Zulip chat and allow the bot to access it
# (see .github/workflows/zulip_emoji_merge_delegate.yaml),
# $NUMBER_OF_COMMENTS_TO_SCAN is optional, but if present, it should be the number of past comments
# that get inspected.  The default value is 50.

ZULIP_API_KEY = sys.argv[1]
ZULIP_EMAIL = sys.argv[2]
ZULIP_SITE = sys.argv[3]
try:
    PAST_COMMENTS = sys.argv[4]
except:
    PAST_COMMENTS = 50

# The script flags any message that contains one of these emoji reactions
emojis=['butterfly', 'robot']
# The script flags any message that contains one of these substrings, ignoring case
substrings=['zenodo']

print(f"Messages with a reaction in {emojis} or containing {substrings} among the last {PAST_COMMENTS} comments")

# Initialize Zulip client
client = zulip.Client(
    email=ZULIP_EMAIL,
    api_key=ZULIP_API_KEY,
    site=ZULIP_SITE
)

# Fetch the messages from the `mathlib reviewers` channel
reviewers_response = client.get_messages({
    "anchor": "newest",
    "num_before": PAST_COMMENTS,
    "num_after": 0,
    # uncomment below if you want to filter better which Zulip channels to scan
    #"narrow": [
    #    {"operator": "channel", "operand": "junk"},
    #],
})

messages=reviewers_response['messages']

for message in messages:
  content = message['content']
  reactions = message['reactions']
  emojiFound=''
  shouldPrint=False
  info=f"#**{message['display_recipient']}>{message['subject']}** "
  # Check for emoji reactions
  for emo in emojis:
    count=0
    for r in reactions:
      if r['emoji_name'] == emo:
        count+=1
    if count != 0:
      emojiFound=f"{emojiFound}{count} {emo} "
      shouldPrint=True
  # Check for substrings
  subs=[]
  for sub in substrings:
    if re.search(f"{sub}", f"{content}", re.IGNORECASE):
      shouldPrint=True
      subs=subs + [sub]
  # Report, if appropriate
  if shouldPrint:
    print(f"\n{info}")
    if emojiFound:
      print(f'* {emojiFound.rstrip()}')
    if subs:
      print(f"* Contains {subs}")
