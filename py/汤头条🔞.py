# -*- coding: utf-8 -*-
# TVBox/影视仓/py-drpy 爬虫源 —— TBR视频
# 站点: https://dpi4.tbrapi.org

import sys
import json
import base64
import hashlib
import re
from datetime import datetime
from urllib.parse import quote, unquote

sys.path.append('..')
from base.spider import Spider as BaseSpider

try:
    import requests
    requests.packages.urllib3.disable_warnings()
except ImportError:
    requests = None

try:
    from Crypto.Cipher import AES
except ImportError:
    AES = None


class Spider(BaseSpider):
    """
    TBR 视频源
    境界: 化龙境(签名验证) + 圣人境(AES解密)
    """

    def getName(self):
        return "TBR"

    def init(self, extend=""):
        pass

    def getDependence(self):
        return []

    def isVideoFormat(self, url):
        return '.m3u8' in str(url) or '.mp4' in str(url) or '.ts' in str(url) or str(url).startswith('magnet:')

    def manualVideoCheck(self):
        return False

    def destroy(self):
        pass

    def liveContent(self, url):
        pass

    # ─── 配置 ─────────────────────────────────────────────────
    host = 'https://dpi4.tbrapi.org'
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "zh-CN,zh;q=0.9",
        "Content-Type": "application/x-www-form-urlencoded",
    }

    _aes_key = '7205a6c3883caf95b52db5b534e12ec3'
    _aes_iv = '81d7beac44a86f43'
    _sign_key = '7205a6c3883caf95b52db5b534e12ec3'
    _img_key = 'f5d965df75336270'
    _img_iv = '97b60394abc2fbe1'

    _system_params = {
        'system_oauth_type': 'pwa',
        'system_oauth_id': 'egzmJgnUCTYIlCxD_1722416055782',
        'system_oauth_new_id': '',
        'system_version': '3.0.1',
        'system_token': '',
        'system_app_type': '',
        'system_build': '',
        'system_build_id': '',
    }

    _class_map = [
        {'type_name': '推荐', 'type_id': 'recommend'},
        {'type_name': '制片厂', 'type_id': 'factory'},
        {'type_name': '最新', 'type_id': 'newest'},
        {'type_name': '经典三级', 'type_id': 'classic'},
        {'type_name': '经典电影', 'type_id': 'classic_movie'},
        {'type_name': '国产', 'type_id': 'domestic'},
        {'type_name': '动漫CG', 'type_id': 'anime'},
        {'type_name': '欧美', 'type_id': 'western'},
        {'type_name': '日韩', 'type_id': 'asian'},
        {'type_name': '小视频', 'type_id': 'smallvideo'},
        {'type_name': '合集', 'type_id': 'compilation'},
        {'type_name': '分类', 'type_id': 'categories'},
    ]

    _tab_id_map = {
        'recommend': '1',
        'factory': '2',
        'newest': '10',
        'classic': '5',
        'classic_movie': '6',
        'domestic': '4',
        'anime': '12',
        'western': '2',
        'asian': '1',
    }

    # ─── 加密工具 ─────────────────────────────────────────────
    def _aes_encrypt(self, plaintext):
        if not AES:
            return ''
        cipher = AES.new(self._aes_key.encode('utf-8'), AES.MODE_CFB, self._aes_iv.encode('utf-8'), segment_size=128)
        return cipher.encrypt(plaintext.encode('utf-8')).hex().upper()

    def _aes_decrypt(self, ciphertext):
        if not AES:
            return ''
        cipher = AES.new(self._aes_key.encode('utf-8'), AES.MODE_CFB, self._aes_iv.encode('utf-8'), segment_size=128)
        decrypted = cipher.decrypt(bytes.fromhex(ciphertext))
        try:
            return decrypted.decode('utf-8')
        except UnicodeDecodeError:
            return decrypted.decode('latin-1')

    def _generate_sign(self, data, timestamp):
        s = 'client=pwa&data=' + data + '&timestamp=' + str(timestamp) + self._sign_key
        return hashlib.md5(hashlib.sha256(s.encode()).hexdigest().encode()).hexdigest()

    # ─── API请求 ──────────────────────────────────────────────
    def _api_request(self, endpoint, params):
        if not requests or not AES:
            return None

        data = dict(self._system_params)
        data.update(params)
        data_json = json.dumps(data, ensure_ascii=False, separators=(',', ':'))

        encrypted_data = self._aes_encrypt(data_json)
        timestamp = int(datetime.now().timestamp())
        sign = self._generate_sign(encrypted_data, timestamp)

        body = {
            'client': 'pwa',
            'timestamp': timestamp,
            'data': encrypted_data,
            'sign': sign,
        }

        try:
            r = requests.post(self.host + endpoint, data=body, headers=self.headers, timeout=10, verify=False)
            r.raise_for_status()
            resp = r.json()
            if 'data' not in resp or not resp['data']:
                return None
            return json.loads(self._aes_decrypt(resp['data']))
        except Exception:
            return None

    # ─── 图片解密 ─────────────────────────────────────────────
    def _decrypt_image_url(self, encrypted_url):
        if not encrypted_url:
            return ''

        if encrypted_url.startswith('http'):
            img_url = encrypted_url
        elif encrypted_url.startswith('{') and '"ori"' in encrypted_url:
            try:
                img_info = json.loads(encrypted_url)
                img_url = img_info.get('ori') or img_info.get('720') or img_info.get('360', '')
                if not img_url or not img_url.startswith('http'):
                    return ''
            except Exception:
                return ''
        elif encrypted_url.isalnum():
            if not AES:
                return ''
            try:
                cipher = AES.new(self._img_key.encode('utf-8'), AES.MODE_CBC, self._img_iv.encode('utf-8'))
                img_url = cipher.decrypt(bytes.fromhex(encrypted_url)).rstrip(b'\x00').decode('utf-8')
            except Exception:
                return ''
        else:
            return ''

        if not img_url.startswith('http'):
            return ''

        img_url_b64 = base64.b64encode(img_url.encode('utf-8')).decode('utf-8')
        base_proxy = self.getProxyUrl() or 'http://127.0.0.1:9980/proxy?do=py'
        sep = '&' if '?' in base_proxy else '?'
        return base_proxy + sep + 'type=tbr_img&url=' + quote(img_url_b64, safe='')

    # ─── 列表提取 ─────────────────────────────────────────────
    def _extract_list(self, api_result):
        video_list = []
        if not api_result or 'data' not in api_result:
            return video_list

        data = api_result['data']
        items = data.get('list', []) if isinstance(data, dict) else (data if isinstance(data, list) else [])

        for item in items:
            try:
                video_list.append({
                    'vod_id': item.get('preview_video', ''),
                    'vod_name': item.get('title', ''),
                    'vod_pic': self._decrypt_image_url(item.get('thumb_cover_str', '')),
                    'vod_remarks': item.get('duration_str', ''),
                })
            except Exception:
                continue
        return video_list

    def _extract_folder(self, api_result, id_prefix, id_field, name_field, pic_field='', remark_field=''):
        video_list = []
        if not api_result or 'data' not in api_result:
            return video_list

        data = api_result['data']
        items = data.get('list', []) if isinstance(data, dict) else (data if isinstance(data, list) else [])

        for item in items:
            try:
                video_list.append({
                    'vod_id': id_prefix + str(item.get(id_field, '')),
                    'vod_name': item.get(name_field, ''),
                    'vod_pic': self._decrypt_image_url(item.get(pic_field, '')) if pic_field else '',
                    'vod_remarks': item.get(remark_field, ''),
                    'vod_tag': 'folder',
                })
            except Exception:
                continue
        return video_list

    def _build_page(self, video_list, page):
        return {
            'list': video_list,
            'page': page,
            'pagecount': 9999,
            'limit': len(video_list),
            'total': 999999,
        }

    # ─── 首页 ─────────────────────────────────────────────────
    def homeContent(self, filter):
        return {'class': list(self._class_map)}

    def homeVideoContent(self):
        result = self._api_request('/pwa.php/api/MvList/recommend', {'page': '1', '_t': '1'})
        return {'list': self._extract_list(result)}

    # ─── 分类 ─────────────────────────────────────────────────
    def categoryContent(self, tid, pg, filter, extend):
        video_list = []
        page = int(pg) if pg else 1

        if tid == 'categories':
            result = self._api_request('/pwa.php/api/MvSearch/getStyle', {})
            if result and 'data' in result:
                data = result['data']
                categories = data.get('list', []) if isinstance(data, dict) else (data if isinstance(data, list) else [])
                for category in categories:
                    if not category.get('child'):
                        continue
                    for sub in category['child']:
                        try:
                            video_list.append({
                                'vod_id': 'style:' + str(sub.get('id', '')),
                                'vod_name': sub.get('name', ''),
                                'vod_pic': '',
                                'vod_remarks': '',
                                'vod_tag': 'folder',
                            })
                        except Exception:
                            continue
            return self._build_page(video_list, page)

        if tid.startswith('style:'):
            style_id = tid[6:]
            result = self._api_request('/pwa.php/api/MvList/style', {
                'page': str(page), 'size': '15', 'id': style_id, 'orderBy': 'id',
            })
            return self._build_page(self._extract_list(result), page)

        if tid.startswith('creator:'):
            uuid = tid[8:]
            result = self._api_request('/pwa.php/api/Creator/featured', {
                'size': '15', 'uuid': uuid, 'lastId': str((page - 1) * 50),
            })
            return self._build_page(self._extract_list(result), page)

        if tid == 'smallvideo':
            tag = extend.get('tag', 'recommend') if isinstance(extend, dict) else 'recommend'
            result = self._api_request('/pwa.php/api/MvList/smallVideoByTag', {
                'page': str(page), 'tag': tag,
            })
            return self._build_page(self._extract_list(result), page)

        if tid == 'compilation':
            result = self._api_request('/pwa.php/api/compilation/list', {'page': str(page), 'sort': 'new'})
            return self._build_page(self._extract_folder(result, 'compilation:', 'id', 'title', 'image', 'date'), page)

        if tid.startswith('compilation:'):
            cid = tid[12:]
            result = self._api_request('/pwa.php/api/compilation/mvlist', {
                'limit': '10', 'id': cid, 'page': str(page),
            })
            return self._build_page(self._extract_list(result), page)

        tab_id = self._tab_id_map.get(tid, '1')

        if tid == 'recommend':
            result = self._api_request('/pwa.php/api/MvList/recommend', {'page': str(page), '_t': '1'})
        elif tid == 'factory':
            result = self._api_request('/pwa.php/api/MvList/featuredzpc', {'page': str(page), '_t': '1'})
        else:
            result = self._api_request('/pwa.php/api/MvList/featured', {
                'page': str(page), 'tabId': tab_id,
            })

        return self._build_page(self._extract_list(result), page)

    # ─── 详情 ─────────────────────────────────────────────────
    def detailContent(self, ids):
        play_url = ids[0] if isinstance(ids, list) else ids
        final_url = play_url.replace('&seconds=30', '')

        return {
            'list': [{
                'vod_id': play_url,
                'vod_name': 'TBR视频',
                'vod_pic': '',
                'vod_content': '',
                'vod_play_from': '播放',
                'vod_play_url': '播放$' + final_url,
            }]
        }

    # ─── 搜索 ─────────────────────────────────────────────────
    def searchContent(self, key, quick, pg="1"):
        page = int(pg) if pg else 1
        result = self._api_request('/pwa.php/api/MvSearch/video', {
            'page': str(page), 'size': '15', 'keyword': key,
        })
        video_list = self._extract_list(result)
        return {
            'list': video_list,
            'page': page,
            'pagecount': 9999,
            'limit': len(video_list),
            'total': 999999,
        }

    # ─── 播放 ─────────────────────────────────────────────────
    def playerContent(self, flag, id, vipFlags):
        return {
            'parse': 0,
            'url': id,
            'header': {
                'User-Agent': self.headers['User-Agent'],
                'Referer': self.host + '/',
            },
        }

    # ─── 本地代理 ─────────────────────────────────────────────
    def localProxy(self, param):
        try:
            params = param if isinstance(param, dict) else {}
            if params.get('type') != 'tbr_img':
                return [404, 'text/plain', 'not found']

            img_url_b64 = params.get('url', '')
            if not img_url_b64:
                return [400, 'text/plain', 'missing url']

            img_url_b64 = unquote(img_url_b64)
            padding = 4 - len(img_url_b64) % 4
            if padding != 4:
                img_url_b64 += '=' * padding

            img_url = base64.b64decode(img_url_b64).decode('utf-8')

            img_headers = {
                'User-Agent': 'Mozilla/5.0 (Linux; Android 10; SM-G973F) AppleWebKit/537.36',
                'Referer': self.host + '/',
            }

            r = requests.get(img_url, headers=img_headers, timeout=10, verify=False)
            if r.status_code != 200:
                return [404, 'text/plain', 'image not found']

            encrypted_data = r.content

            if encrypted_data[:3] == b'\xff\xd8\xff':
                return [200, 'image/jpeg', encrypted_data, {'Content-Length': str(len(encrypted_data))}]
            if encrypted_data[:4] == b'\x89PNG':
                return [200, 'image/png', encrypted_data, {'Content-Length': str(len(encrypted_data))}]

            if not AES:
                return [500, 'text/plain', 'no crypto']

            cipher = AES.new(self._img_key.encode('utf-8'), AES.MODE_CBC, self._img_iv.encode('utf-8'))
            try:
                decrypted = cipher.decrypt(encrypted_data).rstrip(b'\x00')
            except Exception:
                return [500, 'text/plain', 'decryption failed']

            if not decrypted:
                return [500, 'text/plain', 'decryption failed']

            if decrypted[:3] == b'\xff\xd8\xff':
                return [200, 'image/jpeg', decrypted, {'Content-Length': str(len(decrypted))}]
            if decrypted[:4] == b'\x89PNG':
                return [200, 'image/png', decrypted, {'Content-Length': str(len(decrypted))}]
            if len(decrypted) > 12 and decrypted[:4] == b'RIFF' and decrypted[8:12] == b'WEBP':
                return [200, 'image/webp', decrypted, {'Content-Length': str(len(decrypted))}]

            try:
                dec_text = decrypted.decode('ascii', errors='ignore')
                if dec_text[:4] in ('/9j/', 'iVBOR', 'UklGR'):
                    final_img = base64.b64decode(decrypted)
                    if final_img[:3] == b'\xff\xd8\xff':
                        return [200, 'image/jpeg', final_img, {'Content-Length': str(len(final_img))}]
                    if final_img[:4] == b'\x89PNG':
                        return [200, 'image/png', final_img, {'Content-Length': str(len(final_img))}]
            except Exception:
                pass

            return [200, 'image/jpeg', decrypted, {'Content-Length': str(len(decrypted))}]

        except Exception as e:
            return [500, 'text/plain', str(e)]